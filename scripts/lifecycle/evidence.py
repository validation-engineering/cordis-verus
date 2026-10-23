"""Source-bound artifacts and bounded executions shared by lifecycle campaigns."""
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import signal
import time

ROOT = Path(__file__).resolve().parents[2]


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write_json(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n')
    temporary.replace(path)


def module(name):
    path = ROOT / 'scripts' / name
    spec = importlib.util.spec_from_file_location(name.replace('-', '_'), path)
    loaded = importlib.util.module_from_spec(spec)
    exec(compile(path.read_bytes(), str(path), 'exec'), loaded.__dict__)
    return loaded


def inputs():
    return module('record-verification.py').source_hashes()


def environment(offline=True):
    result = os.environ.copy()
    if any(result.get(name) for name in ('RUSTFLAGS','CARGO_ENCODED_RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','VERUS_EXTRA_ARGS','VERUS_Z3_PATH')):
        raise RuntimeError('Custom compiler/verifier overrides are not supported by lifecycle evidence')
    lock = json.loads((ROOT / 'toolchain.lock.json').read_text())
    result['RUSTUP_TOOLCHAIN'] = lock['rust']['channel']
    result['PATH'] = str(Path(result.get('CARGO_HOME', Path.home() / '.cargo')) / 'bin') + os.pathsep + result.get('PATH', '')
    if offline:
        result['CARGO_NET_OFFLINE'] = 'true'
    return result


def invoke(command, directory, label, *, cwd=ROOT, timeout=180, env=None, input_text=None):
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=True)
    row = {'command': list(map(str, command)), 'cwd': str(cwd), 'timeoutSeconds': timeout,
           'timedOut': False, 'interrupted': False, 'evidenceDirectory':str(directory.resolve())}
    started = time.monotonic()
    interruption = None
    try:
        process = subprocess.Popen(row['command'], cwd=cwd, env=env, stdin=subprocess.PIPE,
                                   text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                   start_new_session=True)
        try:
            stdout, stderr = process.communicate(input_text, timeout=timeout)
        except BaseException as error:
            row['timedOut'] = isinstance(error, subprocess.TimeoutExpired)
            row['interrupted'] = not row['timedOut']
            if row['interrupted']: interruption = error
            # Kill descendants too: Cargo/Node/verifier children may inherit
            # the capture pipes and otherwise outlive their failed evidence run.
            if os.name == 'posix':
                # Give nested verification supervisors an interrupt first so
                # they can reap solver groups before releasing their lease.
                try: os.killpg(process.pid, signal.SIGINT)
                except ProcessLookupError: pass
                try:
                    stdout, stderr = process.communicate(timeout=10)
                except BaseException:
                    try: os.killpg(process.pid, signal.SIGKILL)
                    except ProcessLookupError: pass
                    stdout, stderr = process.communicate()
            else:
                subprocess.run(['taskkill', '/PID', str(process.pid), '/T', '/F'], capture_output=True, check=False)
                process.kill()
                stdout, stderr = process.communicate()
        row['returncode'] = process.returncode
    except OSError as error:
        row.update(returncode=None, launchError=str(error))
        stdout, stderr = '', str(error)
    for stream, value in (('stdout', stdout), ('stderr', stderr)):
        path = directory / (label + '.' + stream + '.txt')
        path.write_text(value)
        row[stream] = path.name
        row[stream + 'Sha256'] = digest(path)
    row['elapsedSeconds'] = round(time.monotonic() - started, 3)
    write_json(directory / (label + '.command.json'), row)
    if interruption: raise interruption
    return row, stdout


def checked(row):
    if row['returncode'] != 0 or row['timedOut'] or row['interrupted'] or row.get('launchError'):
        raise RuntimeError('Command failed or is inconclusive: ' + ' '.join(row['command']) + '; see ' + row['stderr'])


def build_native(directory, *, root=ROOT, target=None, offline=True):
    target = Path(target or root / 'target')
    command = ['cargo', 'build', '--locked', '-p', 'cordis-verus', '--example', 'lifecycle_scenario',
               '--target-dir', str(target), '--message-format=json']
    if offline: command.append('--offline')
    row, output = invoke(command, directory, 'native-build', cwd=root, timeout=600, env=environment(offline))
    checked(row)
    artifacts = [json.loads(line) for line in output.splitlines() if line.startswith('{')]
    binaries = [Path(item['executable']) for item in artifacts
                if item.get('reason')=='compiler-artifact' and item.get('target',{}).get('name')=='lifecycle_scenario'
                and item.get('executable')]
    if len(binaries)!=1: raise RuntimeError('Cargo did not emit exactly one lifecycle scenario executable')
    binary=binaries[0]
    row.update(artifact=str(binary), artifactSha256=digest(binary))
    tool, output = invoke(['rustc', '-Vv'], directory, 'rust-toolchain', env=environment(offline))
    checked(tool)
    row['rustc'] = output.strip()
    return binary, row


def execute_native(binary, cases, directory, label='native'):
    command = [str(binary), '--stdio']
    row, output = invoke(command, directory, label, timeout=120,
                         input_text=json.dumps({'cases': cases}, separators=(',', ':')) + '\n')
    row['artifactSha256'] = digest(binary)
    if row['returncode'] != 0 or row['timedOut']:
        return row, None
    try:
        result = json.loads(output)
    except (ValueError, TypeError):
        return row, None
    if (result.get('schema') != 'cordis-verus.lifecycle-execution/v1'
            or result.get('backend') != 'native-managed' or len(result.get('results', [])) != len(cases)):
        return row, None
    return row, result['results']


def new_report(scope, before):
    return {'schema': 'cordis-verus.lifecycle-campaign/v1', 'scope': scope,
            'status': 'running', 'startedAt': datetime.now(timezone.utc).isoformat(),
            'sourceHashes': before, 'releaseAcceptance': False, 'paperCompletion': False,
            'fullNegativeControls': 'not_run', 'python': sys.version, 'cases': []}
