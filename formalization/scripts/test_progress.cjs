const fs=require('fs');const path=require('path');const crypto=require('crypto');
let playwrightPath;
try { playwrightPath=require.resolve('playwright'); }
catch (error) {
 if (error.code!=='MODULE_NOT_FOUND') throw error;
 playwrightPath=path.resolve(__dirname,'../../work/html/runtime/node_modules/playwright');
}
const {chromium}=require(playwrightPath);
const root=path.resolve(__dirname,'..');
const audit=JSON.parse(fs.readFileSync(path.join(root,'proof-status.json'),'utf8'));
const counts=audit.original_theorem_counts;
const mainClosed=['theorem_1_1','theorem_1_2'].every(n=>audit.declarations.find(r=>r.name==='LiLiuGoldbach16.'+n).status==='kernel_closed');
const extra=Object.values(audit.all_public_theorem_counts).reduce((a,b)=>a+b,0)-102;
const definitions=audit.declarations.filter(d=>!['theorem','lemma'].includes(d.source_kind)).length;
const hash=p=>crypto.createHash('sha256').update(fs.readFileSync(p)).digest('hex');
const verification=JSON.parse(fs.readFileSync(path.join(root,'progress-verification.json'),'utf8'));
if(hash(path.join(root,'proof-status.json'))!==verification.input_sha256)throw new Error('HTML audit metadata is stale');
if(hash(path.join(root,'progress.html'))!==verification.html_sha256)throw new Error('HTML differs from build record');
for(const r of audit.source_files)if(hash(path.join(root,r.file))!==r.sha256)throw new Error('Source changed after audit: '+r.file);
(async()=>{
 const browser=await chromium.launch({headless:true,...(process.env.PLAYWRIGHT_CHROMIUM_EXECUTABLE?{executablePath:process.env.PLAYWRIGHT_CHROMIUM_EXECUTABLE}:{}),args:['--no-sandbox']});
 const context=await browser.newContext({viewport:{width:1600,height:1100},offline:true});const page=await context.newPage();let errors=[],network=[];
 page.on('pageerror',e=>errors.push(String(e)));page.on('request',r=>{if(/^https?:/.test(r.url()))network.push(r.url())});
 await page.goto('file://'+path.join(root,'progress.html'));await page.waitForSelector('.item:not([hidden])');
 const visible=()=>page.locator('.item:not([hidden])').count();const check=(x,msg)=>{if(!x)throw new Error(msg)};
 const report={errors,network,source_hashes_match:true,input_sha256:verification.input_sha256,html_sha256:verification.html_sha256};report.initial_visible=await visible();check(report.initial_visible===102,'default 102 reviewed theorems');
 report.original_counts=await page.locator('.stat b').allTextContents();check(report.original_counts.join(',')===[counts.kernel_closed,counts.proof_written_dependencies_pending,counts.pending_direct_sorry].join(','),'original status counts');
 report.warning=await page.locator('#main-warning').innerText();check(report.warning.includes(mainClosed?'传递依赖均未检出 sorryAx':'尚未端到端完成'),'main completeness status');
 report.types=await page.locator('#type-note').innerText();check(report.types.includes('已通过'),'type preservation checked');
 report.math=await page.locator('.katex').count();check(report.math>100,'math rendering');
 report.source_exact=await page.evaluate(()=>{const d=JSON.parse(document.querySelector('#progress-data').textContent);return d.records.every(r=>{const node=document.getElementById(r.id);return Array.from(node.querySelectorAll('.code-line')).map(x=>x.textContent).join('\n')===r.code})});check(report.source_exact,'highlighted actual source');
 await page.locator('.filter-line [data-status="kernel_closed"]').click();report.closed_visible=await visible();check(report.closed_visible===counts.kernel_closed,'closed original');
 await page.locator('.filter-line [data-status="proof_written_dependencies_pending"]').click();report.dependencies_pending_visible=await visible();check(report.dependencies_pending_visible===counts.proof_written_dependencies_pending,'pending dependency original');
 for(const n of ['theorem_1_1','theorem_1_2'])check(await page.locator('#decl-LiLiuGoldbach16-'+n).isVisible()===!mainClosed,n+' pending filter matches audit');
 await page.locator('[data-scope="added"]').click();report.added_visible=await visible();check(report.added_visible===extra,'new helper count');
 await page.locator('#search').fill('badGoldbachMass_le_sqrt');check(await page.locator('#decl-LiLiuGoldbach16-badGoldbachMass_le_sqrt').isVisible(),'helper search');
 await page.locator('#search').fill('');await page.locator('[data-scope="definitions"]').click();report.definitions_visible=await visible();check(report.definitions_visible===definitions,'actual definitions');
 await page.locator('[data-scope="original"]').click();await page.locator('#search').fill('lemma_7_2_convolutions');check(await page.locator('#decl-LiLiuGoldbach16-lemma_7_2_convolutions').isVisible(),'reviewed supplementary theorem');
 await page.locator('#search').fill('');const critical=page.locator('#critical [data-jump]').first();const jump=await critical.count()?critical:page.locator('#main-status [data-jump]').first();const target=await jump.getAttribute('data-jump');await jump.click();check(await page.locator('#decl-'+target.replace(/\./g,'-')).isVisible(),'jump to audited declaration');
 await page.locator('[data-scope="original"]').click();await page.evaluate(()=>window.scrollTo(0,0));await page.screenshot({path:path.join(root,'progress-desktop.png')});
 await page.setViewportSize({width:390,height:844});await page.evaluate(()=>window.scrollTo(0,0));await page.screenshot({path:path.join(root,'progress-mobile.png')});
 report.mobile_width=await page.evaluate(()=>document.documentElement.scrollWidth);check(report.mobile_width===390,'mobile overflow');
 check(errors.length===0,'JS errors');check(network.length===0,'network requests');
 fs.writeFileSync(path.join(root,'progress-browser-verification.json'),JSON.stringify(report,null,2)+'\n');await browser.close();console.log(JSON.stringify(report,null,2));
})().catch(e=>{console.error(e);process.exit(1)});
