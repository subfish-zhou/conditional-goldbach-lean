from pathlib import Path
import json,re,subprocess,hashlib
from project_sources import library_sources, source_declarations
ROOT=Path(__file__).resolve().parents[1];WORK=ROOT/'reference'
base=json.loads((WORK/'declarations.json').read_text());owners={}
pat=re.compile(r'^(?:(?:private|protected)\s+)*(def|abbrev|structure|theorem|lemma)\s+([\w.]+)',re.M)
for p in library_sources():
 for declaration in source_declarations(p):
  name=declaration['name']
  short=name.removeprefix('ConditionalGoldbach.')
  owners[name]={'source_kind':declaration['source_kind'],'file':str(p.relative_to(ROOT)),
    'line':declaration['line'],'original':short in base}
raw=ROOT/'proof-status-raw.json';dump=ROOT/'scripts/Audit.lean'
lean=r'''import ConditionalGoldbach
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut rows : Array Json := #[]
  for (name, info) in env.constants.toList do
    if "ConditionalGoldbach.".isPrefixOf name.toString then
      let axioms ← Lean.collectAxioms name
      let refs := match info.value? (allowOpaque := true) with
        | some value => value.getUsedConstants.map (fun n => toJson n.toString)
        | none => #[]
      let containsSorry := match info.value? (allowOpaque := true) with
        | some value => value.hasSorry
        | none => false
      rows := rows.push <| Json.mkObj [
        ("name",toJson name.toString), ("axioms",toJson (axioms.map Name.toString)),
        ("type_constants",toJson (info.type.getUsedConstants.map Name.toString)),
        ("value_constants",Json.arr refs), ("contains_sorry_directly",toJson containsSorry)]
  liftIO <| IO.FS.writeFile "__OUTPUT__" (Json.arr rows).pretty
'''.replace('__OUTPUT__',str(raw));dump.write_text(lean)
with (ROOT/'audit.log').open('w') as log:
 res=subprocess.run(['lake','env','lean',str(dump.relative_to(ROOT))],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT)
if res.returncode:raise SystemExit('Audit compilation failed; see audit.log')
records=json.loads(raw.read_text());by={r['name']:r for r in records};out=[]
for name,meta in owners.items():
 if name not in by:
  # Private helper names are compiler-generated and are covered by transitive axiom audits.
  if any(r['name'].endswith('.'+name) for r in records):continue
  text=(ROOT/meta['file']).read_text().splitlines()[meta['line']-1]
  if text.startswith('private '):continue
  raise ValueError('Missing public declaration '+name)
 r=by[name]|meta
 r['kernel_closed']=not r['contains_sorry_directly'] and 'sorryAx' not in r['axioms']
 if meta['source_kind'] in ['theorem','lemma']:
  r['status']='pending_direct_sorry' if r['contains_sorry_directly'] else 'proof_written_dependencies_pending' if 'sorryAx' in r['axioms'] else 'kernel_closed'
 else:r['status']='definition_pending_dependencies' if 'sorryAx' in r['axioms'] else 'definition'
 out.append(r)
stub_names={r['name'] for r in records if r['contains_sorry_directly']}
def pending_deps(name):
 seen=set();todo=[name];found=set()
 while todo:
  n=todo.pop()
  if n in seen:continue
  seen.add(n)
  if n in stub_names:found.add(n)
  if n in by:
   todo.extend(x for x in by[n]['type_constants']+by[n]['value_constants'] if x.startswith('ConditionalGoldbach.'))
 return sorted(found)
for r in out:r['pending_local_dependencies']=pending_deps(r['name'])
original=[r for r in out if r['original'] and r['source_kind'] in ['theorem','lemma']]
assert len(original)==102,len(original)
allth=[r for r in out if r['source_kind'] in ['theorem','lemma']]
counts=lambda rs:{k:sum(r['status']==k for r in rs) for k in ['kernel_closed','proof_written_dependencies_pending','pending_direct_sorry']}
result={'scope':'All original 102 theorem declarations plus public implementation helpers; transitive axioms collected by Lean.collectAxioms, including axioms in object definitions.','original_theorem_counts':counts(original),'all_public_theorem_counts':counts(allth),'original_definitions':171,'original_theorems':102,'standard_axioms':['propext','Classical.choice','Quot.sound'],'unusual_axioms':sorted({a for r in out for a in r['axioms'] if a not in ['propext','Classical.choice','Quot.sound','sorryAx']}),'declarations':out,'source_files':[{'file':str(p.relative_to(ROOT)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in library_sources()],'main_results':{n:next(r for r in out if r['name']=='ConditionalGoldbach.'+n)['status'] for n in ['theorem_1_1','theorem_1_2']}}
(ROOT/'proof-status.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='declarations' and k!='source_files'},ensure_ascii=False,indent=2))
