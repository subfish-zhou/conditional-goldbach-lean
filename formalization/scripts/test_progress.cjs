const fs=require('fs');const path=require('path');const crypto=require('crypto');
let playwrightPath;
try { playwrightPath=require.resolve('playwright'); }
catch (error) {
 if (error.code!=='MODULE_NOT_FOUND') throw error;
 playwrightPath=path.resolve(__dirname,'../../work/html/runtime/node_modules/playwright');
}
const {chromium}=require(playwrightPath);
const root=path.resolve(__dirname,'..');
const language=process.argv.includes('--lang')?process.argv[process.argv.indexOf('--lang')+1]:'en';
if(!['en','zh'].includes(language))throw new Error('Expected --lang en or --lang zh');
const zh=language==='zh',pageFile=zh?'progress.zh.html':'progress.html';
const buildFile=zh?'progress-zh-verification.json':'progress-verification.json';
const audit=JSON.parse(fs.readFileSync(path.join(root,'proof-status.json'),'utf8'));
const counts=audit.original_theorem_counts;
const mainClosed=['theorem_1_1','theorem_1_2'].every(n=>audit.declarations.find(r=>r.name==='ConditionalGoldbach.'+n).status==='kernel_closed');
const extra=Object.values(audit.all_public_theorem_counts).reduce((a,b)=>a+b,0)-102;
const definitions=audit.declarations.filter(d=>!['theorem','lemma'].includes(d.source_kind)).length;
const hash=p=>crypto.createHash('sha256').update(fs.readFileSync(p)).digest('hex');
const verification=JSON.parse(fs.readFileSync(path.join(root,buildFile),'utf8'));
if(hash(path.join(root,'proof-status.json'))!==verification.input_sha256)throw new Error('HTML audit metadata is stale');
if(hash(path.join(root,pageFile))!==verification.html_sha256)throw new Error('HTML differs from build record');
for(const r of audit.source_files)if(hash(path.join(root,r.file))!==r.sha256)throw new Error('Source changed after audit: '+r.file);
(async()=>{
 const browser=await chromium.launch({headless:true,...(process.env.PLAYWRIGHT_CHROMIUM_EXECUTABLE?{executablePath:process.env.PLAYWRIGHT_CHROMIUM_EXECUTABLE}:{}),args:['--no-sandbox']});
 const context=await browser.newContext({viewport:{width:1600,height:1100},offline:true});const page=await context.newPage();let errors=[],network=[];
 page.on('pageerror',e=>errors.push(String(e)));page.on('request',r=>{if(/^https?:/.test(r.url()))network.push(r.url())});
 await page.goto('file://'+path.join(root,pageFile));await page.waitForSelector('.item:not([hidden])');
 const visible=()=>page.locator('.item:not([hidden])').count();const check=(x,msg)=>{if(!x)throw new Error(msg)};
 const report={language,errors,network,source_hashes_match:true,input_sha256:verification.input_sha256,html_sha256:verification.html_sha256};check(await page.locator('html').getAttribute('lang')===(zh?'zh-CN':'en'),'page language');
 check(await page.locator('.language-link').count()===2,'language navigation');
 if(!zh)check(await page.locator('.item h2,.math-summary,.audit-line').evaluateAll(nodes=>nodes.every(n=>!/[\u3400-\u9fff]/.test(n.textContent))),'English mathematical explanations');
 report.initial_visible=await visible();check(report.initial_visible===102,'default 102 reviewed theorems');
 report.original_counts=await page.locator('.stat b').allTextContents();check(report.original_counts.join(',')===[counts.kernel_closed,counts.proof_written_dependencies_pending,counts.pending_direct_sorry].join(','),'original status counts');
 report.warning=await page.locator('#main-warning').innerText();check(report.warning.includes(zh?(mainClosed?'传递依赖均未检出 sorryAx':'尚未端到端完成'):(mainClosed?'no sorryAx in their transitive dependencies':'remain incomplete')),'main completeness status');
 report.types=await page.locator('#type-note').innerText();check(report.types.includes(zh?'已通过':'pass Lean definitional-equality checks'),'type preservation checked');
 report.math=await page.locator('.katex').count();check(report.math>100,'math rendering');
 check(await page.locator('.item').count()===102,'initial DOM contains only the active scope');
 report.title_math=await page.locator('.item h2 .katex').count();
 check(!zh||report.title_math>0,'LaTeX in Chinese declaration titles is rendered');
 const exactScope=()=>page.evaluate(()=>{
  const d=JSON.parse(document.querySelector('#progress-data').textContent),lookup=new Map(d.records.map(r=>[r.name,r]));
  return Array.from(document.querySelectorAll('.item')).every(node=>Array.from(node.querySelectorAll('.code-line')).map(x=>x.textContent).join('\n')===lookup.get(node.dataset.name).code);
 });
 report.source_exact=await exactScope();
 for(const scope of ['all','definitions']){await page.locator(`[data-scope="${scope}"]`).click();report.source_exact=report.source_exact&&await exactScope()}
 check(report.source_exact,'highlighted actual source across every scope');
 await page.locator('[data-scope="original"]').click();
 await page.locator('.filter-line [data-status="kernel_closed"]').click();report.closed_visible=await visible();check(report.closed_visible===counts.kernel_closed,'closed original');
 await page.locator('.filter-line [data-status="proof_written_dependencies_pending"]').click();report.dependencies_pending_visible=await visible();check(report.dependencies_pending_visible===counts.proof_written_dependencies_pending,'pending dependency original');
 for(const n of ['theorem_1_1','theorem_1_2'])check(await page.locator('#decl-ConditionalGoldbach-'+n).isVisible()===!mainClosed,n+' pending filter matches audit');
 await page.locator('[data-scope="added"]').click();report.added_visible=await visible();check(report.added_visible===extra,'new helper count');
 await page.locator('#search').fill('badGoldbachMass_le_sqrt');check(await page.locator('#decl-ConditionalGoldbach-badGoldbachMass_le_sqrt').isVisible(),'helper search');
 await page.locator('#search').fill('');await page.locator('[data-scope="definitions"]').click();report.definitions_visible=await visible();check(report.definitions_visible===definitions,'actual definitions');
 await page.locator('[data-scope="original"]').click();await page.locator('#search').fill('lemma_7_2_convolutions');check(await page.locator('#decl-ConditionalGoldbach-lemma_7_2_convolutions').isVisible(),'reviewed supplementary theorem');
 await page.locator('#search').fill('');const critical=page.locator('#critical [data-jump]').first();const jump=await critical.count()?critical:page.locator('#main-status [data-jump]').first();const target=await jump.getAttribute('data-jump');await jump.click();check(await page.locator('#decl-'+target.replace(/\./g,'-')).isVisible(),'jump to audited declaration');
 await page.locator('[data-scope="definitions"]').click();await page.waitForTimeout(1900);check(errors.length===0,'removing a jumped-to item before its highlight timer completes');
 await page.locator('[data-scope="original"]').click();await page.evaluate(()=>window.scrollTo(0,0));await page.screenshot({path:path.join(root,zh?'progress-zh-desktop.png':'progress-desktop.png')});
 await page.setViewportSize({width:390,height:844});await page.evaluate(()=>window.scrollTo(0,0));await page.screenshot({path:path.join(root,zh?'progress-zh-mobile.png':'progress-mobile.png')});
 await page.goto('file://'+path.join(root,pageFile)+'#decl-ConditionalGoldbach-badGoldbachMass_le_sqrt');
 await page.waitForSelector('#decl-ConditionalGoldbach-badGoldbachMass_le_sqrt');
 check(await page.locator('#decl-ConditionalGoldbach-badGoldbachMass_le_sqrt').isVisible(),'fragment navigation loads helper');
 await page.reload();await page.waitForSelector('#decl-ConditionalGoldbach-badGoldbachMass_le_sqrt');
 check(await page.locator('#decl-ConditionalGoldbach-badGoldbachMass_le_sqrt').isVisible(),'initial deep link loads helper');
 report.mobile_width=await page.evaluate(()=>document.documentElement.scrollWidth);check(report.mobile_width===390,'mobile overflow');
 check(errors.length===0,'JS errors');check(network.length===0,'network requests');
 fs.writeFileSync(path.join(root,zh?'progress-zh-browser-verification.json':'progress-browser-verification.json'),JSON.stringify(report,null,2)+'\n');await browser.close();console.log(JSON.stringify(report,null,2));
})().catch(e=>{console.error(e);process.exit(1)});
