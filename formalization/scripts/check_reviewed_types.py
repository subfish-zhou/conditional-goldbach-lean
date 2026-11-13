"""Verify the current theorem types against the original reviewed snapshot in Lean.
The snapshot namespace is renamed, then its local constants are mapped to current
constants. Lean's definitional equality checks all 102 complete theorem types.
Universe parameter names are alpha-renamed positionally before comparison, with equal arity required.
This checks preservation of the complete reviewed theorem statements.
"""
from pathlib import Path
import json,subprocess
ROOT=Path(__file__).resolve().parents[1];WORK=ROOT/'reference'
source=(WORK/'Reviewed.lean').read_text().replace('ConditionalGoldbach','ReviewBaseline')
source='import ConditionalGoldbach\n'+source
names=[n for n,r in json.loads((WORK/'declarations.json').read_text()).items() if r['kind']=='theorem']
checks='\n'.join('    '+json.dumps(n)+',' for n in names)
script=r'''
open Lean Elab Command Meta in
run_cmd do
  let names : Array String := #[__NAMES__]
  let env ← getEnv
  let mut rows : Array Json := #[]
  for s in names do
    let oldName := ("ReviewBaseline." ++ s).toName
    let newName := ("ConditionalGoldbach." ++ s).toName
    let oldInfo := env.find? oldName |>.get!
    let newInfo := env.find? newName |>.get!
    let mapped := oldInfo.type.replace fun e =>
      match e with
      | .const n us =>
          if "ReviewBaseline.".isPrefixOf n.toString then
            some (.const ((n.toString.replace "ReviewBaseline." "ConditionalGoldbach.").toName) us)
          else none
      | _ => none
    unless oldInfo.levelParams.length == newInfo.levelParams.length do
      throwError "Reviewed theorem universe arity changed: {s}"
    let alignedNew := newInfo.type.instantiateLevelParams newInfo.levelParams
      (oldInfo.levelParams.map Level.param)
    let ok ← liftTermElabM <| Meta.isDefEq mapped alignedNew
    rows := rows.push <| Json.mkObj [("name",toJson newName.toString),("reviewed_type_preserved",toJson ok)]
    unless ok do throwError "Reviewed theorem type changed: {s}"
  liftIO <| IO.FS.writeFile "__OUTPUT__" (Json.arr rows).pretty
'''.replace('__NAMES__',checks.rstrip(',\n')).replace('__OUTPUT__',str(ROOT/'reviewed-types.json'))
path=ROOT/'scripts/ReviewedTypes.lean';path.write_text(source+'\n'+script)
with (ROOT/'reviewed-types.log').open('w') as log:
 p=subprocess.run(['lake','env','lean',str(path.relative_to(ROOT))],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT)
if p.returncode:raise SystemExit('Type preservation check failed; see reviewed-types.log')
rows=json.loads((ROOT/'reviewed-types.json').read_text());assert len(rows)==102 and all(r['reviewed_type_preserved'] for r in rows)
print('All 102 reviewed theorem types are definitionally equal to their current types.')
