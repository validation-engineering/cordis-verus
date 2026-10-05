#!/usr/bin/env node
/** Assemble local, verified default-core artifacts. Never downloads or publishes. */
import { copyFile, lstat, mkdir, mkdtemp, realpath, rename, rm, writeFile } from 'node:fs/promises';
import { basename, dirname, isAbsolute, join, relative, resolve, sep } from 'node:path';
import { fileURLToPath } from 'node:url';
import { verifyNativeManifest } from '../packages/compat-cordis/native-artifacts.js';

const contains = (parent, child) => { const part=relative(parent,child); return !isAbsolute(part) && part!=='..' && !part.startsWith('..'+sep); };
export async function assembleNativeBundle(inputs, output) {
  if (!Array.isArray(inputs) || !inputs.length) throw new Error('At least one native directory is required');
  const bundles=inputs.map(path=>verifyNativeManifest(path));
  output=resolve(output);
  let ancestor=output; const pending=[];
  while (true) {
    try { output=join(await realpath(ancestor),...pending); break; }
    catch (error) { if (error.code!=='ENOENT') throw error; pending.unshift(basename(ancestor)); ancestor=dirname(ancestor); }
  }
  for (const bundle of bundles) if (contains(bundle.directory,output) || contains(output,bundle.directory)) throw new Error('Output cannot overlap an input native directory');
  try { await lstat(output); throw new Error('Output directory already exists'); }
  catch (error) { if (error.code!=='ENOENT') throw error; }
  const entries=[], seen=new Set(); let source;
  for (const bundle of bundles) for (const artifact of bundle.artifacts) {
    if (seen.has(artifact.entry.target)) throw new Error('Duplicate native target: '+artifact.entry.target);
    seen.add(artifact.entry.target);
    if (source && source!==artifact.provenance.build.sourceDigest) throw new Error('Native inputs belong to different source snapshots');
    source=artifact.provenance.build.sourceDigest; entries.push(artifact);
  }
  await mkdir(dirname(output),{recursive:true});
  const temporary=await mkdtemp(join(dirname(output),'.native-bundle-'));
  try {
    const artifacts=[];
    for (const artifact of entries.sort((a,b)=>a.entry.target.localeCompare(b.entry.target))) {
      const file='prebuilds/'+artifact.entry.target+'/cordis.node';
      const provenance='provenance/'+artifact.entry.target+'.json';
      await mkdir(dirname(join(temporary,file)),{recursive:true});
      await mkdir(dirname(join(temporary,provenance)),{recursive:true});
      await copyFile(artifact.path,join(temporary,file));
      await copyFile(artifact.provenancePath,join(temporary,provenance));
      artifacts.push({...artifact.entry,file,provenance});
    }
    const manifest={...bundles[0].manifest,artifacts};
    await writeFile(join(temporary,'manifest.json'),JSON.stringify(manifest,null,2)+'\n');
    verifyNativeManifest(temporary);
    // Exclusive directory creation prevents replacing an existing bundle.
    await mkdir(output);
    try { for (const name of ['manifest.json','prebuilds','provenance']) await rename(join(temporary,name),join(output,name)); }
    catch (error) { await rm(output,{recursive:true,force:true}); throw error; }
    return verifyNativeManifest(output);
  } finally { await rm(temporary,{recursive:true,force:true}); }
}
if (process.argv[1] && resolve(process.argv[1])===fileURLToPath(import.meta.url)) {
  const [flag,output,...inputs]=process.argv.slice(2);
  if (flag!=='--output' || !output || !inputs.length) throw new Error('Usage: package-native.mjs --output <new-directory> <native-directory> [...]');
  const bundle=await assembleNativeBundle(inputs,output);
  console.log(JSON.stringify({directory:bundle.directory,manifestSha256:bundle.manifestSha256,targets:bundle.artifacts.map(item=>item.entry.target),uploaded:false,validation:'preserves input host evidence; no foreign execution'},null,2));
}
