import '../../packages/compat-cordis/register.js';
import { Context } from '../../packages/compat-cordis/index.js';
import { Loader } from '../../packages/compat-loader/index.js';
const context = new Context();
const loader = new Loader(context);
try {
  await loader.loadFile(new URL('./cordis.json', import.meta.url));
  console.log(context.greeting.hello('Cordis'));
  await loader.update('greeting', { config: { prefix: 'Welcome' } });
  console.log(context.greeting.hello('Cordis'));
} finally {
  await loader.dispose();
  await context.dispose();
}
