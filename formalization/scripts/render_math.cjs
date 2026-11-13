const fs = require('fs');
let katex; try { katex = require('katex'); } catch { katex = require('../../work/html/runtime/node_modules/katex'); }
const formulas = JSON.parse(fs.readFileSync(0, 'utf8'));
const rendered = {}, errors = [];
for (const f of formulas) {
  try {
    rendered[f.id] = katex.renderToString(f.tex, {
      displayMode: f.display, output: 'htmlAndMathml',
      throwOnError: true, strict: 'error', trust: false,
      maxExpand: 1000,
    });
  } catch (e) {
    errors.push({id: f.id, tex: f.tex, error: String(e)});
  }
}
process.stdout.write(JSON.stringify({version:katex.version, rendered, errors}));
if (errors.length) process.exitCode = 1;
