const fs=require('fs'),path=require('path'),crypto=require('crypto');
let playwrightPath;
try { playwrightPath=require.resolve('playwright'); }
catch (error) {
 if (error.code!=='MODULE_NOT_FOUND') throw error;
 playwrightPath=path.resolve(__dirname,'../../../work/html/runtime/node_modules/playwright');
}
const {chromium}=require(playwrightPath);
const check=(b,msg)=>{if(!b)throw new Error(msg)};
(async()=>{
 const browser=await chromium.launch({headless:true,...(process.env.PLAYWRIGHT_CHROMIUM_EXECUTABLE?{executablePath:process.env.PLAYWRIGHT_CHROMIUM_EXECUTABLE}:{}),args:['--no-sandbox']});
 const context=await browser.newContext({offline:true,viewport:{width:1500,height:1100}});
 const page=await context.newPage(),errors=[],network=[];
 page.on('pageerror',e=>errors.push(String(e)));
 page.on('request',r=>{if(/^https?:/.test(r.url()))network.push(r.url())});
 await page.goto('file://'+path.join(__dirname,'report.html'));
 check(await page.locator('.item').count()===103,'103 independent statement cards');
 const math=await page.locator('.katex').count();check(math>100,'rendered Chinese-side math');
 check(await page.locator('.highlight span').count()>100,'Lean syntax highlighting');
 check(await page.locator('body').evaluate(e=>e.scrollWidth<=innerWidth),'desktop horizontal overflow');
 await page.screenshot({path:path.join(__dirname,'report-desktop.png')});
 await page.locator('#search').fill('proposition_6_5');
 await page.waitForFunction(()=>document.querySelectorAll('.item:not([hidden])').length===3);
 check(await page.locator('.item:not([hidden])').count()===3,'Prop 6.5 and two specification helpers');
 const text=await page.locator('.item[data-search^="proposition_6_5 "]').innerText();
 check(text.includes('arithmeticOperator')&&text.includes('diagonalOperator')&&text.includes('modelOperator'),'Prop 6.5 all three operators');
 await page.locator('#search').fill('');
 await page.setViewportSize({width:390,height:844});
 check(await page.locator('body').evaluate(e=>e.scrollWidth<=innerWidth),'mobile horizontal overflow');
 await page.screenshot({path:path.join(__dirname,'report-mobile.png')});
 check(errors.length===0,'browser errors');check(network.length===0,'remote runtime requests');
 const result={passed:true,statement_cards:103,rendered_math:math,errors,network,offline:true,
   html_sha256:crypto.createHash('sha256').update(fs.readFileSync(path.join(__dirname,'report.html'))).digest('hex')};
 fs.writeFileSync(path.join(__dirname,'report-browser.json'),JSON.stringify(result,null,2)+'\n');
 console.log(JSON.stringify(result));await browser.close();
})().catch(e=>{console.error(e);process.exit(1)});
