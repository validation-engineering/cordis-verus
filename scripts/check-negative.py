#!/usr/bin/env python3
"""Require proof failures for precise, compilable mutations of executable code."""

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
sys.dont_write_bytecode = True


def toolchain():
    spec = importlib.util.spec_from_file_location("cordis_installer", ROOT / "scripts/install-verus.py")
    installer = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(installer)
    lock = installer.LOCK
    binary = ROOT / ".tools" / lock["verus"]["assets"][installer.platform_key()]["directory"] / "verus"
    environment = os.environ.copy()
    cargo = Path(environment.get("CARGO_HOME", str(Path.home() / ".cargo"))) / "bin"
    environment["PATH"] = str(cargo) + os.pathsep + environment.get("PATH", "")
    environment["RUSTUP_TOOLCHAIN"] = lock["rust"]["channel"]
    return binary, environment


def run_verus(binary, environment, source, report_path, compile_only=False, *, threads=9, timeout=600):
    command = [
        str(binary), str(source), "--crate-name", "cordis_negative", "--crate-type=lib",
        "--edition=2021", "--no-cheating", "--output-json", "--triggers-mode", "silent",
        "--num-threads", str(threads),
    ]
    if compile_only:
        command += ["--no-verify", "--compile", "-o", str(source.parent / "compile-check.rlib")]
    try:
        result = subprocess.run(command, env=environment, text=True, capture_output=True, timeout=timeout)
    except subprocess.TimeoutExpired as error:
        # subprocess may expose bytes even when text=True. Keep partial output
        # for diagnosis, but never turn a timed-out process into proof evidence.
        for suffix, output in ((".stdout.json", error.stdout), (".stderr.txt", error.stderr)):
            if isinstance(output, bytes):
                output = output.decode("utf-8", errors="replace")
            report_path.with_suffix(suffix).write_text(output or "")
        raise
    report_path.with_suffix(".stdout.json").write_text(result.stdout)
    report_path.with_suffix(".stderr.txt").write_text(result.stderr)
    return result


def rejected_result(name, result):
    """Accept only a complete-crate run with a concrete failed contract."""
    try:
        stats = json.loads(result.stdout)["verification-results"]
        rejected = (
            result.returncode != 0 and stats["success"] is False
            and stats["encountered-vir-error"] is False
            and type(stats["verified"]) is int and stats["verified"] > 0
            and type(stats["errors"]) is int and stats["errors"] > 0
            and stats["is-verifying-entire-crate"] is True
        )
    except (ValueError, KeyError, TypeError):
        raise RuntimeError(f"Mutation {name} produced no complete verification results") from None
    if not rejected:
        raise RuntimeError(f"Mutation {name} was not rejected by full-crate proof checking")
    if not any(line.startswith(message) for line in result.stderr.splitlines() for message in (
        "error: postcondition not satisfied", "error: precondition not satisfied",
        "error: assertion failed", "error: invariant not satisfied",
        "error: possible arithmetic underflow/overflow", "error: decreases not satisfied",
    )):
        raise RuntimeError(f"Mutation {name} has no conclusive contract failure")
    # A real failed contract must not hide a partial, resource-limited or crashed
    # whole-crate run. Rendered source excerpts are data, not diagnostics.
    resource = re.compile(
        r"rlimit|resource.limit|timed? out|timeout|solver.*unknown|"
        r"internal compiler error|panicked at|segmentation fault|killed by|out of memory",
        re.IGNORECASE,
    )
    for line in result.stderr.splitlines():
        if not re.match(r"\s*(?:[0-9]+)?\s*\|", line) and resource.search(line):
            raise RuntimeError(f"Mutation {name} has a resource or compiler failure; this is not accepted proof evidence")
    return {"name": name, "compiles": True, "verification-results": stats}


def check_mutation(mutation, baseline, temporary, reports, binary, environment, *, threads=9, timeout=600, runner=run_verus):
    name, relative, original, replacement = mutation
    mutated = temporary / name
    shutil.copytree(baseline, mutated)
    source = mutated / relative
    text = source.read_text()
    if text.count(original) != 1:
        raise RuntimeError(f"Mutation {name} no longer has exactly one source match; update the negative check")
    source.write_text(text.replace(original, replacement))
    try:
        compiled = runner(binary, environment, mutated / "lib.rs", reports / f"{name}-compile", True,
                          threads=threads, timeout=timeout)
        if compiled.returncode != 0:
            raise RuntimeError(f"Mutation {name} did not compile; this is not an accepted proof failure")
        failed = runner(binary, environment, mutated / "lib.rs", reports / name,
                        threads=threads, timeout=timeout)
    except subprocess.TimeoutExpired:
        raise RuntimeError(f"Mutation {name} timed out; this is not an accepted proof failure") from None
    return rejected_result(name, failed)


def check_mutations(mutations, baseline, temporary, reports, binary, environment, *, jobs=1, threads=9, timeout=600, runner=run_verus):
    """Use isolated source trees and preserve manifest order in the report."""
    results = [None] * len(mutations)
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        pending = {pool.submit(check_mutation, mutation, baseline, temporary, reports, binary,
                               environment, threads=threads, timeout=timeout, runner=runner): index
                   for index, mutation in enumerate(mutations)}
        try:
            for future in as_completed(pending):
                index = pending[future]
                result = future.result()
                results[index] = result
                stats = result["verification-results"]
                print(f"OK {result['name']}: compiles; proof rejected ({stats['verified']} verified, {stats['errors']} errors)", flush=True)
        except BaseException:
            for future in pending:
                future.cancel()
            raise
    return results


def positive(value):
    number = int(value)
    if number < 1:
        raise argparse.ArgumentTypeError("must be a positive integer")
    return number


def mutation_manifest():
    """The canonical ordered set of source mutations required by release evidence."""
    return [
        (
            "provider-lifetime-guard", "lib.rs",
            "if l.binding.provider == id && (!node.present || node.phase == Phase::Inactive || node.restoring) { return Err(Error::Relied); }",
            "// Negative test: provider lifetime guard intentionally removed.",
        ),
        (
            "cleanup-stack-fifo", "effects.rs",
            "self.tokens.pop()",
            "if self.tokens.len() == 0 { None } else { Some(self.tokens.remove(0)) }",
        ),
        (
            "provision-conflict-guard", "lib.rs",
            "if d.provides && d.port == p && self.nodes[d.owner].present { return false; }",
            "// Negative test: registered provision conflict guard removed.",
        ),
        (
            "inverse-restores-wrong-cell", "resources.rs",
            "self.cells.set(inverse.index, inverse.before);",
            "self.cells.set(inverse.index, inverse.after);",
        ),
        (
            "compaction-drops-live-bindings", "lib.rs",
            "if self.links[i].live {",
            "if !self.links[i].live {",
        ),
        (
            "stage-loses-pending-admission", "episode.rs",
            "if self.in_flight { return true; }",
            "if self.in_flight { return false; }",
        ),
        (
            "support-ignores-provider", "progress.rs",
            "ok = ok && selected[p];",
            "ok = ok;",
        ),
        (
            "journal-restores-first-inverse", "history.rs",
            "let inverse = self.entries.pop().unwrap();",
            "let inverse = self.entries.remove(0);",
        ),
        (
            "episode-token-names-wrong-inverse", "witnessed.rs",
            "let token = self.journal.len();",
            "let token = 0;",
        ),
        (
            "child-inverse-retires-parent", "ownership.rs",
            "match kernel.retire(child) {",
            "match kernel.retire(self.actor) {",
        ),
        (
            "child-handle-ignores-episode-generation", "ownership.rs",
            "if kernel.episode_generation(self.actor) != Some(expected) {",
            "if false {",
        ),
        (
            "begin-reuses-episode-generation", "lib.rs",
            "node.generation += 1;",
            "node.generation += 0;",
        ),
        (
            "driver-skips-resource-recovery", "driver.rs",
            "let _restored = self.episodes[id].rollback();",
            "let _restored = true;",
        ),
        (
            "normal-form-ignores-retirement", "global.rs",
            "&& left.fibers[n].retired == right.fibers[n].retired",
            "&& true",
        ),
        (
            "renaming-leaves-stale-provider", "alpha.rs",
            "provider: (r.forward)(b.provider)",
            "provider: b.provider",
        ),
        (
            "dynamic-stage-discards-real-inverse", "canonical.rs",
            "machine.inverses[owner as int].push(yielded.1)),",
            "machine.inverses[owner as int].push(|s: S| s)),",
        ),
        (
            "iterator-fuel-does-not-decrease", "termination.rs",
            "&&& label.1 == control::Rule::Iter ==> after[label.0 as int] < before[label.0 as int]",
            "&&& label.1 == control::Rule::Iter ==> after[label.0 as int] <= before[label.0 as int]",
        ),
        (
            "program-copy-ignores-source", "program.rs",
            "Instruction::Copy{source,index,next} => (index,self.episode.read(source).unwrap(),next),",
            "Instruction::Copy{source:_,index,next} => (index,0,next),",
        ),
        (
            "atomic-landing-skips-target-check", "program.rs",
            "match self.kernel.leave_if_changed(id) {\n            Ok(()) => {\n                self.episodes[id].cancel();",
            "match Err::<(), Error>(Error::Changed) {\n            Ok(()) => {\n                self.episodes[id].cancel();",
        ),
        (
            "api-insertion-reuses-historical-name", "program_refinement.rs",
            "n == a.allocated && z.allocated == a.allocated+1",
            "n <= a.allocated && z.allocated == a.allocated+1",
        ),
        (
            "provision-inverse-ignores-domain", "mediated.rs",
            "undo: |x: IMap<K, V>| if x.dom().contains(key) { Some(x.remove(key)) } else { None }, next",
            "undo: |x: IMap<K, V>| Some(x.remove(key)), next",
        ),
        (
            "coeffect-independence-discards-outcome", "partial_independence.rs",
            "a.unwrap().outcome == b.unwrap().outcome\n            && mediated::partial_related",
            "true\n            && mediated::partial_related",
        ),
        (
            "interception-reverses-metadata-order", "contexts.rs",
            "{Some((c.providers[k])((m.merge)(k,mu,(c.carried)(k))))} else {None}",
            "{Some((c.providers[k])((m.merge)(k,(c.carried)(k),mu)))} else {None}",
        ),
        (
            "child-removal-ignores-retained-token", "child_history.rs",
            "==> kind(token) != Some(child)\n}",
            "==> kind(token) != Some(child) || a.control.fibers[child].retired\n}",
        ),
        (
            "iterator-lift-reverses-inverse-composition", "iterators.rs",
            "f::Tracked { value: tail.value, undo: f::compose(first.undo, tail.undo) }",
            "f::Tracked { value: tail.value, undo: f::compose(tail.undo, first.undo) }",
        ),
        (
            "iterator-run-discards-continuation", "iterators.rs",
            "run(family, yielded.next, (fuel - 1) as nat, current)",
            "run(family, None, (fuel - 1) as nat, current)",
        ),
        (
            "erasure-drops-parent-read", "deletion.rs",
            "&&& (rule == c::Rule::Insert ==> z.control.fibers[actor].parent != Some(removed))",
            "&&& (rule == c::Rule::Insert ==> true)",
        ),
        (
            "entangled-recovery-loses-restriction", "entangled.rs",
            "Action::Restriction { key } => state.remove(key),",
            "Action::Restriction { key: _ } => state,",
        ),
        (
            "normal-form-counts-phantom-stages", "program_refinement.rs",
            "(x.depths[n]-1) as nat).next < x.codes[n].len())",
            "(x.depths[n]-1) as nat).next <= x.codes[n].len())",
        ),
        (
            "model-allows-undeclared-provision", "preservation.rs",
            "&& z.tables[actor].dom().subset_of(a.control.fibers[actor].provisions)",
            "&& true",
        ),
        (
            "observational-local-is-uniform", "observational_algebra.rs",
            "        == (forall|s: S| #[trigger] eq((effect(input).undo)(effect(s).value), s)),",
            "        == eq((effect(input).undo)(effect(input).value), input),",
        ),
        (
            "dependent-operation-loses-outcome-fiber", "dependent_grammar.rs",
            "&&& (lib.outcomes)(a,y.outcome)",
            "&&& true",
        ),
        (
            "grammar-inverse-forgets-captured-provider", "grammar_lift.rs",
            "inverse:Inverse::Operation {provider,key,undo:y.undo}",
            "inverse:Inverse::Operation {provider:actor,key,undo:y.undo}",
        ),
        (
            'grammar-repeat-call-uses-fresh-token',
            'grammar_lift.rs',
            'first_call(a.history,actor,a.state.iterators[actor].unwrap(),a.state)',
            'a.history.len()',
        ),
        (
            'child-driver-removal-ignores-journals',
            'child_driver.rs',
            'if self.has_reference(id) {return Err(ChildDriverError::Retained);}',
            'if false && self.has_reference(id) {return Err(ChildDriverError::Retained);}',
        ),
        (
            'child-driver-skips-drift-diversion',
            'child_driver.rs',
            'if !has_target {\n                    proof {self.kernel.paper_observations(id);}',
            'if false && !has_target {\n                    proof {self.kernel.paper_observations(id);}',
        ),
        (
            'dependent-landing-drops-continuation',
            'dependent_lift.rs',
            'roots:a.roots,current:a.current.insert(actor,next),history:a.history.push(e)',
            'roots:a.roots,current:a.current.insert(actor,None),history:a.history.push(e)',
        ),
        (
            'grammar-inverse-origin-fifo-token',
            'grammar_ordering.rs',
            'token==tokens.last() && before==input && after==next',
            'token==tokens.first() && before==input && after==next',
        ),
        (
            "unload-state-map-forgets-actual-stack", "rule_frames.rs",
            "Source::Restoration{actor,tokens:a.accumulators[actor]}",
            "Source::Restoration{actor,tokens:Seq::empty()}",
        ),
        (
            'iterator-independence-discards-continuation', 'iterator_independence.rs',
            'q::continuation(|i:I,j:I|q::iterator_related(eq,family,i,j),a.next,b.next)',
            'true',
        ),
        (
            'indexed-model-forgets-inverse-token', 'indexed_ordering.rs',
            'local_model(s::Yield {state:out.state,inverse:a.history.len(),next:dl::marker(out.next)},receipt_history(a.history))',
            'local_model(s::Yield {state:out.state,inverse:0,next:dl::marker(out.next)},receipt_history(a.history))',
        ),
        (
            'mixed-removal-ignores-retention', 'mixed_grammar.rs',
            '&& ch::remove_unreferenced(kind(a.history),a.state,actor)',
            '&& true',
        ),
        (
            'mixed-child-inverse-skips-retirement', 'mixed_grammar.rs',
            'if s::registered(a,child) {Some(s::with_control(a,global::retire_fiber(a.control,child)))} else {None}',
            'if s::registered(a,child) {Some(a)} else {None}',
        ),
        (
            'grammar-recovery-discards-restriction', 'grammar_recovery.rs',
            'gl::Inverse::Provision {key}=>e::Action::Restriction {key},',
            'gl::Inverse::Provision {key:_}=>e::Action::Identity,',
        ),
        (
            'mixed-origin-skips-inverse-context', 'mixed_ordering.rs',
            'invokes(history,tokens.drop_last(),next,actor,token,before,after)',
            'invokes(history,tokens.drop_last(),input,actor,token,before,after)',
        ),
        (
            'mixed-recovery-child-corrupts-table', 'mixed_recovery.rs',
            'mx::Receipt::Child {..}=>e::Action::Identity',
            'mx::Receipt::Child {..}=>e::Action::Restriction {key:Port {key:0,realm:0}}',
        ),
        (
            'iterator-bridge-compares-failed-foreign-map', 'iterator_bridge.rs',
            'requires stable(eq,family,id,map),map(s).is_some(),',
            'requires stable(eq,family,id,map),map(s).is_none(),',
        ),
        (
            'mixed-transposition-ignores-parent-read', 'mixed_transposition.rs',
            'insertion_ready(lib,programs,b,id,parent,dependencies,provisions,root),parent!=Some(child),',
            'insertion_ready(lib,programs,b,id,parent,dependencies,provisions,root),',
        ),
        (
            'recovery-example-inverse-adds-again', 'recovery_examples.rs',
            'undo:|after:int|Some(after-amount)',
            'undo:|after:int|Some(after+amount)',
        ),
        (
            'mixed-transport-drops-new-receipt', 'mixed_transport.rs',
            'history:if g::landing(left,next,rule) {right.history.push(next.history.last())} else {right.history}',
            'history:right.history',
        ),
        (
            'observational-witness-discards-recovery', 'observational_grammar.rs',
            'operation_respects(eq,op) && operation_witness(eq,op)',
            'operation_respects(eq,op)',
        ),
        (
            'observational-journal-discards-commutation', 'observational_recovery.rs',
            'k!=j || forall|v:V| #[trigger] eq(k,f(g(v)),g(f(v)))',
            'true',
        ),
        (
            'mixed-retire-actor-read-bypass', 'mixed_orchestration.rs',
            'requires s::registered(a.state,id),s::registered(a.state,actor),id!=actor,',
            'requires s::registered(a.state,id),s::registered(a.state,actor),',
        ),
        (
            'mixed-remove-provider-read-bypass', 'mixed_orchestration.rs',
            'requires inv::well_formed(a.state),s::registered(a.state,id),a.state.control.fibers[id].phase==crate::Phase::Inactive,\n        id!=actor,g::run(lib,node,a.state,actor).is_some(),',
            'requires inv::well_formed(a.state),s::registered(a.state,id),\n        id!=actor,g::run(lib,node,a.state,actor).is_some(),',
        ),
        (
            'causal-suffix-history-bypass', 'causal_normalization.rs',
            'let moved=transport::transport(states.subrange(i+2,states.len() as int),labels.subrange(i+2,labels.len() as int),reverse);',
            'let moved=states.subrange(i+2,states.len() as int);',
        ),
        (
            'administrative-self-retire-bypass', 'administrative_orchestration.rs',
            '&& !(rule==r::Rule::Begin && external==r::Rule::Retire && actor==id)',
            '&& true',
        ),
        (
            'strict-journal-forgets-foreign-inverse', 'strict_journal.rs',
            'crosses(eq,journal(prefix),e.forward) && crosses(eq,journal(prefix),e.inverse)',
            'crosses(eq,journal(prefix),e.forward)',
        ),
        (
            'unload-captured-child-bypass',
            'unload_orchestration.rs',
            'external==r::Rule::Remove && id!=actor && no_child(a.history,a.state.accumulators[actor],id)',
            'external==r::Rule::Remove && id!=actor',
        ),
        (
            'isolated-history-counts-deleted-entry', 'isolated_deletion.rs',
            'g::owner(history[token as int-1].landed.receipt)==removed {0nat} else {1nat}',
            'g::owner(history[token as int-1].landed.receipt)==removed {1nat} else {1nat}',
        ),
        (
            'rewrite-receipt-correspondence-bypass',
            'rewrite_confluence.rs',
            'a.len()==z.len() && forall|i:int| 0<=i<a.len() ==> tr::related(a[i],z[i])',
            'a.len()==z.len() && forall|i:int| 0<=i<a.len() ==> a[i].state==z[i].state && a[i].roots==z[i].roots && a[i].current==z[i].current',
        ),
        (
            'iteration-forward-only-bypass', 'mixed_iteration_exchange.rs',
            '|| pi::value_independent(|u:U,v:U|eq((lib.key)(a),u,v),(lib.apply)(a,x),(lib.apply)(b,y))',
            '|| pi::commutes(|u:U,v:U|eq((lib.key)(a),u,v),pi::value_forward((lib.apply)(a,x)),pi::value_forward((lib.apply)(b,y)))',
        ),
        (
            'entangled-loading-drops-pinning', 'entangled_loading.rs',
            'forall|owner:usize| gr::installed(state,owner) ==> gr::pinned(state,owner)',
            'true',
        ),
        (
            'shared-history-reuses-source-landing', 'shared_execution.rs',
            'g::land(lib,programs,target,actor,next.state.control.fibers[actor].phase)',
            'g::land(lib,programs,source,actor,next.state.control.fibers[actor].phase)',
        ),
        (
            'shared-outcome-stability-bypass', 'shared_replay.rs',
            '==> pi::value_independent(|u:U,v:U|eq((lib.key)(a),u,v),(lib.apply)(a,x),(lib.apply)(b,y))',
            '==> (forall|f:m::PartialMap<U>,g:m::PartialMap<U>| #![trigger pi::value_generators((lib.apply)(a,x)).contains(f),pi::value_generators((lib.apply)(b,y)).contains(g)] pi::value_generators((lib.apply)(a,x)).contains(f) && pi::value_generators((lib.apply)(b,y)).contains(g) ==> pi::commutes(|u:U,v:U|eq((lib.key)(a),u,v),f,g))',
        ),
        (
            'mixed-driver-xor-skips-payload', 'mixed_driver.rs',
            'self.write_slot(provider,index,Some(value^mask));\n                Inverse::Xor {provider,key,mask}',
            'self.write_slot(provider,index,Some(value));\n                Inverse::Xor {provider,key,mask}',
        ),
        (
            'observational-runs-domain-bypass',
            'mixed_observational_runs.rs',
            '    &&& a.control==b.control\n    &&& forall|id:usize| s::registered(a,id) ==> {\n        &&& a.tables[id].dom()==b.tables[id].dom()\n        &&& forall|key:Port| a.tables[id].dom().contains(key) ==> eq(key,a.tables[id][key],b.tables[id][key])\n    }',
            '    &&& a.control==b.control\n    &&& forall|id:usize| s::registered(a,id) ==> {\n        &&& forall|key:Port| a.tables[id].dom().contains(key) ==> eq(key,a.tables[id][key],b.tables[id][key])\n    }',
        ),
        (
            'observational-receipts-projection-bypass',
            'mixed_observational_runs.rs',
            'requires exchange::mixed_names(left,right),m::partial_related(pi::context_eq(eq),exchange::inverse(left),exchange::inverse(right)),',
            'requires exchange::mixed_names(left,right),',
        ),
        (
            'observational-token-renaming-bypass',
            'mixed_observational_transport.rs',
            'Seq::new(source.len(),|i:int|token(h,source[i]))',
            'source',
        ),
        (
            'foreign-inverse-discards-reverse-witness',
            'foreign_unload.rs',
            'inverse:prior[token as int].forward,own:false',
            'inverse:identity(),own:false',
        ),
        (
            'external-input-forgets-parent-renaming',
            'external_inputs.rs',
            'actor:(rho.forward)(actor),parent:names::parent(rho,parent),dependencies,provisions,root:(h.forward)(root)',
            'actor:(rho.forward)(actor),parent,dependencies,provisions,root:(h.forward)(root)',
        ),
        (
            'fresh-history-name-support',
            'fresh_grammar.rs',
            '.union(ISet::new(|name:usize|exists|i:int|0<=i<a.history.len() && entry_names(action,a.history[i]).contains(name)))',
            '.union(ISet::empty())',
        ),
        (
            'fresh-landing-discards-allocation-choice',
            'fresh_semantics.rs',
            'landed:run(lib,programs(actor)(iterator),a.state,actor,choice).unwrap()',
            'landed:run(lib,programs(actor)(iterator),a.state,actor,None).unwrap()',
        ),
        (
            'allocation-child-provision-collision',
            'allocation_inputs.rs',
            'pub open spec fn key_b()->Port {Port {key:1,realm:0}}',
            'pub open spec fn key_b()->Port {Port {key:0,realm:0}}',
        ),
        (
            'fresh-driver-child-blueprint',
            'fresh_driver.rs',
            'super::Instruction::Child {blueprint,next,..}=>super::Instruction::Child {expected:draft.rows.len(),blueprint,next},',
            'super::Instruction::Child {blueprint:_,next,..}=>super::Instruction::Child {expected:draft.rows.len(),blueprint:0,next},',
        ),
        (
            'shared-unload-keeps-uncompressed-token',
            'shared_unload_execution.rs',
            'tokens.map(|_i:int,t:nat|index(history,offset,owner,t))',
            'tokens.map(|_i:int,t:nat|t)',
        ),
        (
            'fresh-equivariance-retains-literal-parent',
            'fresh_equivariance.rs',
            '==crate::mixed_transposition::insert(f::configuration(rho,h,a),(rho.forward)(actor),names::parent(rho,parent),dependencies,provisions,(h.forward)(root))',
            '==crate::mixed_transposition::insert(f::configuration(rho,h,a),(rho.forward)(actor),parent,dependencies,provisions,(h.forward)(root))',
        ),
        (
            'guarded-child-domain-success-only',
            'guarded_child_domains.rs',
            '            && p::project(left.state,keys)==p::project(right.state,keys)\n            ==> #[trigger] defined(left)==#[trigger] defined(right)',
            '            && p::project(left.state,keys)==p::project(right.state,keys)\n            && defined(left) && defined(right)\n            ==> #[trigger] defined(left)==#[trigger] defined(right)',
        ),
        (
            'admitted-fresh-generation-guard',
            'admitted_fresh_driver.rs',
            'if draft.kernel.episode_generation(actor)!=Some(self.generation) {return Err(AdmissionError::StaleAdmission);}',
            'let _unchecked_generation=draft.kernel.episode_generation(actor);',
        ),
        (
            'admitted-script-event-provenance',
            'admitted_script.rs',
            'events.push(ScriptEvent {action_index:i,effect});',
            'events.push(ScriptEvent {action_index:i+1,effect});',
        ),
        (
            'selective-recovery-forgets-owner-foreign-crossing',
            'selective_foreign_recovery.rs',
            '(!records[i].own || !call.own)',
            '(!records[i].own && !call.own)',
        ),
        (
            'providing-owner-publication-guard-bypass',
            'providing_owner_transport.rs',
            '        deletion::separated(source.state,owner),s::registered(source.state,actor),actor!=owner,',
            '        s::registered(source.state,actor),actor!=owner,',
        ),
        (
            'strict-batch-redo-guard-bypass',
            'strict_batch_recovery.rs',
            '        p::commutes(eq,foreign,redo),p::commutes(eq,foreign,undo),',
            '        p::commutes(eq,foreign,undo),',
        ),
        (
            'strict-batch-old-record-retraction',
            'strict_batch_recovery.rs',
            '        !fu::retracts(tables_equal(),fu::Pair {forward:old_events()[0].forward,inverse:old_events()[0].inverse,own:false},cut()),\n        m::run',
            '        fu::retracts(tables_equal(),fu::Pair {forward:old_events()[0].forward,inverse:old_events()[0].inverse,own:false},cut()),\n        m::run',
        ),
        (
            'orchestration-support-cycle-parent-blocks-removal',
            'orchestration_support_cycle.rs',
            't::insert(a2,2,Some(1),',
            't::insert(a2,2,Some(0),',
        ),
        (
            'old-receipt-current-domain-bypass',
            'old_receipt_support.rs',
            '        g::run(lib,programs(actor)(old.iterator),old.input,actor)==Some(old.landed),g::undo(old.landed.receipt,current).is_some(),',
            '        g::run(lib,programs(actor)(old.iterator),old.input,actor)==Some(old.landed),',
        ),
        (
            'old-journal-provider-guard-bypass',
            'old_journal_unload.rs',
            '        state.control.fibers[owner].phase!=Phase::Inactive,!r::relied(state.control,actor),',
            '        state.control.fibers[owner].phase!=Phase::Inactive,',
        ),
        (
            'old-journal-terminal-phase-bypass',
            'old_journal_closure.rs',
            '        target_proof::controls(z,out,owner),source_proof::separated(z.state,owner),z.state.control.fibers[owner].phase==Phase::Unloading,',
            '        target_proof::controls(z,out,owner),source_proof::separated(z.state,owner),',
        ),
        (
            'observational-permutation-forgets-commutation',
            'observational_permutation.rs',
            'witnessed(eq,effects),commuting(eq,p::returned(effects,x)),p::permutation(order,effects.len()),',
            'witnessed(eq,effects),p::permutation(order,effects.len()),',
        ),
        (
            'component-totality-drops-provision-obligation',
            'paper_invariants.rs',
            '==> provisions.subset_of(owned(it::run(family,Some(root),fuel,f::unit(input)).current.value).dom())',
            '==> true',
        ),
        (
            'functional-quotient-begin-own-root',
            'functional_quotient.rs',
            'r::Rule::Begin=>s::edit(b,n,Phase::Loading,z.control.fibers[n].committed,Some(b.effects[n]),Seq::empty()),',
            'r::Rule::Begin=>s::edit(b,n,Phase::Loading,z.control.fibers[n].committed,Some(a.effects[n]),Seq::empty()),',
        ),
        (
            'old-journal-own-as-foreign',
            'old_journal_interleaving.rs',
            '        0<=j<fu::catalog(actions.drop_last()).len(),fu::catalog(actions.drop_last())[j].own,\n        !fu::event(fu::catalog(actions.drop_last()),actions.last()).own,',
            '        0<=j<fu::catalog(actions.drop_last()).len(),fu::catalog(actions.drop_last())[j].own,',
        ),
        (
            'mixed-age-token-identity',
            'mixed_age_unload.rs',
            '        let token=tokens.last();let mapped=history::index(left,offset,owner,token);',
            '        let token=tokens.last();let mapped=token;',
        ),
        (
            'old-provision-without-installed-owner',
            'old_provision_support.rs',
            'current.control.fibers[owner].phase!=Phase::Inactive,!r::relied(current.control,actor),\n        g::undo(receipt::<U>(actor,key),current).is_some(),',
            '!r::relied(current.control,actor),\n        g::undo(receipt::<U>(actor,key),current).is_some(),',
        ),
        (
            'configuration-enabled-polarity',
            'configuration_entry.rs',
            '        !self.disabled\n',
            '        self.disabled\n',
        ),
        (
            'resolution-completion-missing-retirement',
            'resolution_completion_counterexample.rs',
            '    let a3=orchestration::retire(a2,0);',
            '    let a3=a2;',
        ),
        (
            'old-provision-journal-finishes-before-cut',
            'old_provision_journal_example.rs',
            'select:|_:()|if actor==2 && stage==1 {Some(2nat)}else{None}',
            'select:|_:()|None',
        ),
        (
            'internal-old-owner-capture',
            'internal_old_unload.rs',
            '        prefix.push(if g::landing(a,z,label.1) {fu::Action::Forward {call:fu::entry_pair(lib,programs,g::entry(lib,programs,a,label.0),owner)}} else {fu::Action::Identity})',
            '        prefix.push(if g::landing(a,z,label.1) {fu::Action::Forward {call:fu::entry_pair(lib,programs,g::entry(lib,programs,a,label.0),label.0)}} else {fu::Action::Identity})',
        ),
        (
            'derived-recovery-keeps-discarded-handle',
            'effect_realization.rs',
            'Some((heap.remove(child),parent))',
            'Some((heap.remove(child),child))',
        ),
        (
            'interface-outside-frame',
            'interface_observation.rs',
            'requires o::related_maps(observed(eq,keys,project),f,g),map_frame(keys,project,f),map_frame(keys,project,g),',
            'requires o::related_maps(observed(eq,keys,project),f,g),map_frame(keys,project,f),',
        ),
        (
            'internal-table-inactive-phase',
            'internal_table_unload.rs',
            's::registered(a.state,owner),a.state.control.fibers[owner].phase==Phase::Inactive,',
            's::registered(a.state,owner),true,',
        ),
        (
            'generalized-table-rejects-new-provision',
            'generalized_table_deletion.rs',
            'source_proof::table_node(node)\n    }',
            'source_proof::table_node(node) && (labels[i].0!=owner ==> replay::operational_mixed(node))\n    }',
        ),
        (
            'foreign-provision-target-domain',
            'foreign_provision_transport.rs',
            'requires s::registered(target,actor),source.control.fibers[actor]==target.control.fibers[actor],source.tables[actor].dom()==target.tables[actor].dom(),',
            'requires s::registered(target,actor),source.control.fibers[actor]==target.control.fibers[actor],',
        ),
        (
            'dependent-independence-discards-yield-stability',
            'dependent_independence.rs',
            '==> p::value_independent(|u:U,v:U|eq((l.key)(a),u,v),(l.apply)(a,x),(r.apply)(b,y))',
            '==> (forall|f:m::PartialMap<U>,g:m::PartialMap<U>| #![trigger p::value_generators((l.apply)(a,x)).contains(f),p::value_generators((r.apply)(b,y)).contains(g)] p::value_generators((l.apply)(a,x)).contains(f) && p::value_generators((r.apply)(b,y)).contains(g) ==> p::commutes(|u:U,v:U|eq((l.key)(a),u,v),f,g))',
        ),
        (
            'dynamic-insert-ignores-private-dependency',
            'dynamic_table_registry.rs',
            'actor!=owner && (rule==r::Rule::Insert ==> z.state.control.fibers[actor].dependencies.disjoint(a.state.control.fibers[owner].provisions))',
            'actor!=owner',
        ),
        (
            'strict-partial-quotient-ignores-inverse-word',
            'strict_partial_quotient.rs',
            '|input:s::State<U>|g::restore(a.history,a.state.accumulators[actor],input,actor)',
            '|input:s::State<U>|g::restore(a.history,Seq::empty(),input,actor)',
        ),
        (
            'strict-partial-quotient-per-forgets-symmetry',
            'strict_partial_quotient_per.rs',
            '&&& forall|x:S,y:S| #[trigger] eq(x,y) ==> eq(y,x)',
            '&&& true',
        ),
        (
            'strict-alias-ignores-static-primitive',
            'strict_partial_quotient_reflexive.rs',
            'requires inv::well_formed(a),d::permitted(lib,ISet::full(),ISet::full(),node),dep::run(lib,node,a,actor).is_some(),',
            'requires inv::well_formed(a),dep::run(lib,node,a,actor).is_some(),',
        ),
        (
            'paper-component-missing-leastness',
            'paper_components.rs',
            'it::paper_witnessed(|a:G,b:G|observed(eq,coeffects,c.dependencies.union(c.provisions),a,b),family,c.root)',
            'it::witnessed(|a:G,b:G|observed(eq,coeffects,c.dependencies.union(c.provisions),a,b),family,c.root)',
        ),
        (
            'paper-observation-active-accumulator-erased',
            'paper_observations.rs',
            '(Theta::Active {accumulator:g,committed:a},Theta::Active {accumulator:h,committed:b})=>a==b && o::related_maps(base,g,h),',
            '(Theta::Active {accumulator:g,committed:a},Theta::Active {accumulator:h,committed:b})=>a==b,',
        ),
        (
            'paper-confinement-wrong-read-registry',
            'paper_confinement.rs',
            '    &&& forall|m:N,k:K| p::registered(view,a,m) && d.contains(k)\n        ==> p::lookup(view,a,m,k)==p::lookup(view,b,m,k)',
            '    &&& forall|m:N,k:K| p::registered(view,b,m) && d.contains(k)\n        ==> p::lookup(view,a,m,k)==p::lookup(view,b,m,k)',
        ),
        (
            'foreign-child-owner-guard',
            'foreign_child_transport.rs',
            'actor!=owner && match programs(actor)(a.current[actor].unwrap())',
            'match programs(actor)(a.current[actor].unwrap())',
        ),
        (
            'paper-instantiation-captured-parent',
            'paper_instantiation.rs',
            'Some(state)=>Some(Landing {state,name:child,inverse:Receipt{child},next:body(child)}),',
            'Some(state)=>Some(Landing {state,name:child,inverse:Receipt{child:parent},next:body(child)}),',
        ),
        (
            'foreign-child-private-dependency-guard',
            'foreign_child_deletion.rs',
            'source_proof::table_node(node) || child::guard(programs,source[i],labels[i].0,owner)',
            'source_proof::table_node(node) || (labels[i].0!=owner && child::child_node(node))',
        ),
        (
            'paper-trace-child-dependencies',
            'paper_trace_independence.rs',
            'a.dependencies==b.dependencies && a.provisions==b.provisions && relation((left,a.root),(right,b.root))',
            'true && a.provisions==b.provisions && relation((left,a.root),(right,b.root))',
        ),
    ]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=positive, default=os.environ.get("CORDIS_NEGATIVE_JOBS", "1"),
                        help="independent mutation workers (default: CORDIS_NEGATIVE_JOBS or 1)")
    parser.add_argument("--threads", type=positive,
                        help="Verus threads per worker (default: share a nine-thread budget)")
    parser.add_argument("--timeout", type=positive, default=os.environ.get("CORDIS_NEGATIVE_TIMEOUT", "600"),
                        help="wall-clock seconds per subprocess (default: CORDIS_NEGATIVE_TIMEOUT or 600); timeout never counts as rejection")
    args = parser.parse_args()
    threads = args.threads or max(1, 9 // args.jobs)
    timeout = args.timeout
    binary, environment = toolchain()
    reports = ROOT / "target/proof-negative"
    reports.mkdir(parents=True, exist_ok=True)
    (reports / "report.json").unlink(missing_ok=True)
    mutations = mutation_manifest()
    with tempfile.TemporaryDirectory(prefix="cordis-negative-") as temporary:
        temporary = Path(temporary)
        baseline = temporary / "baseline"
        shutil.copytree(ROOT / "crates/cordis-kernel/src", baseline)
        try:
            result = run_verus(binary, environment, baseline / "lib.rs", reports / "baseline", timeout=timeout)
        except subprocess.TimeoutExpired:
            sys.exit(f"Unmodified kernel timed out; no proof evidence recorded; see {reports}")
        if result.returncode != 0:
            sys.exit(f"Unmodified kernel failed verification; see {reports / 'baseline.stderr.txt'}")
        baseline_json = json.loads(result.stdout)
        baseline_stats = baseline_json["verification-results"]
        if (not baseline_stats["success"] or baseline_stats["errors"] != 0
                or baseline_stats["verified"] == 0 or baseline_stats["encountered-vir-error"]
                or not baseline_stats["is-verifying-entire-crate"]):
            sys.exit("Unmodified kernel did not produce a successful, nonempty verification report")
        print(f"OK unmodified kernel: {baseline_stats['verified']} verified, 0 errors", flush=True)
        summary = {"verus": baseline_json["verus"], "baseline": baseline_stats,
                   "execution": {"jobs": args.jobs, "threadsPerWorker": threads, "timeoutSeconds": timeout},
                   "mutations": []}
        print(f"Checking {len(mutations)} mutations with {args.jobs} worker(s), {threads} Verus threads per worker", flush=True)
        try:
            summary["mutations"] = check_mutations(mutations, baseline, temporary, reports, binary,
                                                  environment, jobs=args.jobs, threads=threads, timeout=timeout)
        except RuntimeError as error:
            sys.exit(f"{error}; see {reports}")
        (reports / "report.json").write_text(json.dumps(summary, indent=2) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
