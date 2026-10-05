import {createHash} from 'node:crypto';
import {readdir,readFile,readlink} from 'node:fs/promises';
import path from 'node:path';

// Hash installed runner code as well as the lock. Vite-generated caches are
// outputs, not inputs; workspace package sources are hashed by each caller.
export async function installedDependencyEvidence(root) {
  const entries=[];
  const excluded=['.vite','.vite-temp','.cache'];
  async function walk(directory) {
    for(const entry of (await readdir(directory,{withFileTypes:true})).sort((a,b)=>a.name.localeCompare(b.name))) {
      if(excluded.includes(entry.name))continue;
      const filename=path.join(directory,entry.name);
      const relative=path.relative(root,filename);
      if(entry.isDirectory())await walk(filename);
      else if(entry.isSymbolicLink())entries.push([relative,`link:${await readlink(filename)}`]);
      else if(entry.isFile())entries.push([relative,createHash('sha256').update(await readFile(filename)).digest('hex')]);
    }
  }
  await walk(path.join(root,'node_modules'));
  return {sha256:createHash('sha256').update(JSON.stringify(entries)).digest('hex'),files:entries.length,excludedGeneratedDirectories:excluded};
}
