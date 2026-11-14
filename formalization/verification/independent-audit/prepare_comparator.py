"""Stage independent TeX references for the Lean 4.35 built-in comparator.

Challenge and Solution share frozen reference definitions. The solution must
inhabit the *independent* full propositions using the original library proofs.
A second check compares the entire independent proposition to the original
theorem type (including universe arity), so a weaker expected proposition is
not accepted merely because it follows from the original theorem.
"""
from pathlib import Path
import hashlib, json, re, shutil

audit = Path(__file__).resolve().parent
project = audit.parents[1]
out = audit / 'comparator-project'
modules = out / 'TexAuditComparator'
modules.mkdir(parents=True, exist_ok=True)
groups = [('sections-1-4', 'Expected.lean', 'Reference14'),
          ('sections-5-7', 'Reference.lean', 'Reference57'),
          ('appendices', 'Reference.lean', 'ReferenceAB')]
rows, definitions, frozen, semantic_bridges, bridge_modules = [], [], {}, [], []
numerical_cross_checks = []
for group, filename, module in groups:
    folder = audit / group
    for name in [filename, 'comparison.json', 'definitions-comparison.json']:
        p = folder / name
        frozen[str(p.relative_to(audit))] = hashlib.sha256(p.read_bytes()).hexdigest()
    shutil.copy2(folder / filename, modules / f'{module}.lean')
    rows += [{**r, 'audit_group': group} for r in json.loads((folder/'comparison.json').read_text())]
    definitions += [{**r, 'audit_group': group} for r in json.loads((folder/'definitions-comparison.json').read_text())]
    bridge = folder/'Bridges.lean'
    if bridge.exists():
        bridge_module = module.replace('Reference', 'Bridges')
        bridge_modules.append(bridge_module)
        shutil.copy2(bridge, modules/f'{bridge_module}.lean')
        frozen[str(bridge.relative_to(audit))] = hashlib.sha256(bridge.read_bytes()).hexdigest()
        namespace = {'sections-1-4':'TexAudit14', 'sections-5-7':'TexAudit57'}[group]
        semantic_bridges += [namespace+'.'+n for n in re.findall(r'^theorem (\w+)', bridge.read_text(), re.M)]
assert len({r['actual'] for r in rows}) == len(rows)
numeric = audit/'appendices/NumericCrossCheck.lean'
if numeric.exists():
    shutil.copy2(numeric, modules/'NumericCrossCheck.lean')
    frozen[str(numeric.relative_to(audit))]=hashlib.sha256(numeric.read_bytes()).hexdigest()
    bridge_modules.append('NumericCrossCheck')
    numerical_cross_checks.append('TexAuditAB.Numeric.unorderedPrimePairs_eq_905')
original = json.loads((project/'reference/declarations.json').read_text())
original_theorems = {'ConditionalGoldbach.'+n for n,d in original.items() if d['kind']=='theorem'}
assert original_theorems <= {r['actual'] for r in rows}
(out/'lean-toolchain').write_text((project/'lean-toolchain').read_text())
(out/'lakefile.toml').write_text('name = "independentTexAudit"\nversion = "0.1.0"\ndefaultTargets = ["TexAuditComparator"]\n\n[[require]]\nname = "conditionalGoldbach"\npath = "../../.."\n\n[[lean_lib]]\nname = "TexAuditComparator"\n')
manifest = json.loads((project/'lake-manifest.json').read_text())
manifest['name'] = 'independentTexAudit'
for p in manifest['packages']: p['inherited'] = True
manifest['packages'].insert(0, dict(type='path', scope='', name='conditionalGoldbach',
    manifestFile='lake-manifest.json', inherited=False, dir='../../..', copy=False,
    configFile='lakefile.toml'))
(out/'lake-manifest.json').write_text(json.dumps(manifest, indent=2)+'\n')
(out/'.lake').mkdir(exist_ok=True)
if not (out/'.lake/packages').exists():
    (out/'.lake/packages').symlink_to('../../../../.lake/packages', target_is_directory=True)
header = '\n'.join('import TexAuditComparator.'+m for _,_,m in groups)
header += ''.join('\nimport TexAuditComparator.'+m for m in bridge_modules)
header += '\n\nset_option autoImplicit false\nset_option maxHeartbeats 0\nnoncomputable section\nuniverse u\nnamespace TexComparator\n'
challenge, solution = header, header
targets = semantic_bridges.copy()+numerical_cross_checks
for i,r in enumerate(rows):
    short = f'statement_{i:03d}_'+r['actual'].split('.')[-1]
    levels = r.get('universe_params', [])
    expected = r['expected'] + ('.{'+', '.join(levels)+'}' if levels else '')
    typ = expected
    challenge += f'\n-- {r["label"]}; TeX {r["tex_lines"]}\ntheorem {short} : {typ} := by sorry\n'
    solution += f'\ntheorem {short} : {typ} := by\n  exact @{r["actual"]}\n'
    targets.append('TexComparator.'+short)
    r['comparator_target'] = targets[-1]
for i,r in enumerate(definitions):
    short = f'definition_{i:03d}_'+r['actual'].split('.')[-1]
    levels = r.get('universe_params', [])
    expected = r['expected'] + ('.{'+', '.join(levels)+'}' if levels else '')
    typ = f'@{expected} = @{r["actual"]}'
    challenge += f'\ntheorem {short} : {typ} := by sorry\n'
    solution += f'\ntheorem {short} : {typ} := rfl\n'
    targets.append('TexComparator.'+short)
    r['comparator_target'] = targets[-1]
challenge += '\nend TexComparator\n'
solution += '\nend TexComparator\n'
(modules/'Challenge.lean').write_text(challenge)
(modules/'Solution.lean').write_text(solution)
(out/'TexAuditComparator.lean').write_text('import TexAuditComparator.Solution\n')
config = dict(challenge_module='TexAuditComparator.Challenge',
              solution_module='TexAuditComparator.Solution', theorem_names=targets,
              permitted_axioms=['propext','Quot.sound','Classical.choice'])
(out/'comparator.json').write_text(json.dumps(config, indent=2)+'\n')
(audit/'comparator-manifest.json').write_text(json.dumps(dict(
    statement_count=len(rows), definition_body_count=len(definitions),
    target_count=len(targets), original_theorems_covered=len(original_theorems), semantic_bridges=semantic_bridges,
    numerical_cross_checks=numerical_cross_checks,
    statements=rows, definitions=definitions, frozen_references=frozen), ensure_ascii=False, indent=2)+'\n')
checks = ',\n'.join('    ('+json.dumps(r['expected'])+', '+json.dumps(r['actual'])+')' for r in rows)
checker = '\n'.join('import TexAuditComparator.'+m for _,_,m in groups)+'\n'
checker += r'''
open Lean Elab Command Meta in
run_cmd do
  let names : Array (String × String) := #[__CHECKS__]
  let env ← getEnv
  let mut rows : Array Json := #[]
  for (reference, actual) in names do
    let referenceInfo := env.find? reference.toName |>.get!
    let actualInfo := env.find? actual.toName |>.get!
    let .defnInfo d := referenceInfo | throwError "Expected a Prop definition: {reference}"
    unless d.levelParams.length == actualInfo.levelParams.length do
      throwError "Universe arity mismatch: {reference}, {actual}"
    let actualType := actualInfo.type.instantiateLevelParams actualInfo.levelParams
      (d.levelParams.map Level.param)
    let ok ← liftTermElabM <| Meta.isDefEq d.value actualType
    unless ok do throwError "Independent full type mismatch: {reference}, {actual}"
    rows := rows.push <| Json.mkObj [("expected", toJson reference), ("actual", toJson actual),
      ("full_type_definitionally_equal", toJson ok),
      ("universe_arity", toJson d.levelParams.length)]
  liftIO <| IO.FS.writeFile "__OUTPUT__" (Json.arr rows).pretty
'''.replace('__CHECKS__',checks).replace('__OUTPUT__','../independent-full-types.json')
(modules/'CheckTypes.lean').write_text(checker)
controls = {
  'condition': (
    'theorem check (n : Nat) (h : 0 < n) : n = n := rfl',
    'theorem check (n : Nat) (h : 1 < n) : n = n := rfl'),
  'quantifier': (
    'theorem check : ∀ n : Nat, ∃ m : Nat, m = m := by intro n; exact ⟨0, rfl⟩',
    'theorem check : ∃ m : Nat, ∀ n : Nat, m = m := by exact ⟨0, fun _ => rfl⟩'),
  'definition': (
    'def Predicate (n : Nat) : Prop := n = n\ntheorem check (n : Nat) : Predicate n := rfl',
    'def Predicate (n : Nat) : Prop := True\ntheorem check (n : Nat) : Predicate n := True.intro')}
for name,(left,right) in controls.items():
    for side,body in [('Challenge',left),('Solution',right)]:
        (modules/f'Control{name.title()}{side}.lean').write_text('namespace ComparatorControl\n'+body+'\nend ComparatorControl\n')
    (out/f'control-{name}.json').write_text(json.dumps(dict(
        challenge_module=f'TexAuditComparator.Control{name.title()}Challenge',
        solution_module=f'TexAuditComparator.Control{name.title()}Solution',
        theorem_names=['ComparatorControl.check'], permitted_axioms=config['permitted_axioms']),indent=2)+'\n')
print(json.dumps(dict(statements=len(rows), definitions=len(definitions), targets=len(targets)),indent=2))
