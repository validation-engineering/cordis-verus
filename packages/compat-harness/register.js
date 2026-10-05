import { registerProfile } from '@cordis-verus/compat-cordis/bootstrap';
export const registration = registerProfile('harness', new URL('./index.js', import.meta.url).href, new URL('./index.cjs', import.meta.url).href);
