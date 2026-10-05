import { registerProfile } from './bootstrap.js';
export const registration = registerProfile('cordis', new URL('./index.js', import.meta.url).href, new URL('./index.cjs', import.meta.url).href);
