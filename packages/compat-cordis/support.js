export function defineProperty(target, key, value) {
  Object.defineProperty(target, key, {value, writable: true, configurable: true});
  return target;
}

// Equivalent ASCII word splitting to cosmokit's hyphenate helper; no runtime
// dependency is needed by the portable facade's logger name formatting.
export function hyphenate(source) {
  let result='', state='delimiter';
  for (let index=0; index<source.length; index++) {
    const character=source[index], code=source.charCodeAt(index);
    if (code>=65 && code<=90) {
      const next=source.charCodeAt(index+1);
      if (state==='upper' ? next>=97 && next<=122 : state!=='delimiter') result+='-';
      result+=character.toLowerCase(); state='upper';
    } else if (code>=97 && code<=122) {
      result+=character; state='lower';
    } else if (character==='-' || character==='_') {
      if (state!=='delimiter') result+='-';
      state='delimiter';
    } else result+=character;
  }
  return result;
}
