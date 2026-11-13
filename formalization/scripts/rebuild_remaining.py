"""Keep every audited statement in the project exactly once.
Original statement bodies not yet implemented remain explicit sorry obligations.
No proof status is inferred merely from whether a theorem has a tactic script.
"""
from pathlib import Path
import re,json
from project_sources import source_declarations
ROOT=Path(__file__).resolve().parents[1];WORK=ROOT/'reference'
d=json.loads((WORK/'declarations.json').read_text());pre=(WORK/'preamble.txt').read_text()
drafts_path=ROOT/'draft-modules.json'
drafts=set(json.loads(drafts_path.read_text())['modules']) if drafts_path.exists() else set()
# Diagnostic scratch modules are not part of the proof library.
drafts.update(p.stem for p in (ROOT/'ConditionalGoldbach/Proofs').glob('*.lean') if p.stem.endswith(('Check','Axioms')))
claimed={};pattern=re.compile(r'^(?:(?:private|protected)\s+)*(?:theorem|lemma|def|abbrev|structure)\s+([\w.]+)',re.M)
for p in (ROOT/'ConditionalGoldbach').rglob('*.lean'):
 if p.name=='Remaining.lean' or p.stem in drafts:continue
 for declaration in source_declarations(p):
  name=declaration['name'].removeprefix('ConditionalGoldbach.')
  if name in claimed:raise ValueError(f'Duplicate source declaration {name}: {p}, {claimed[name]}')
  claimed[name]=str(p.relative_to(ROOT))
pending=[n for n,r in d.items() if r['kind']=='theorem' and n not in claimed]
imports=['ConditionalGoldbach.Proofs.'+p.stem for p in sorted((ROOT/'ConditionalGoldbach/Proofs').glob('*.lean')) if p.stem not in drafts]
header=('Complete import index: all 102 reviewed theorem obligations have proof implementations.' if not pending else 'Remaining exact audited statements. Each sorry is an outstanding proof, not an axiom certified by the paper audit.')
text='\n'.join('import '+n for n in imports)+'\n\n/-! '+header+' -/\n'+pre+'\n\n'.join(d[n]['code'] for n in pending)+'\n\nend ConditionalGoldbach\n'
(ROOT/'ConditionalGoldbach/Remaining.lean').write_text(text)
(ROOT/'ConditionalGoldbach.lean').write_text('import ConditionalGoldbach.Remaining\n')
(ROOT/'source-coverage.json').write_text(json.dumps({'original_declarations':273,'original_theorems':102,'direct_stubs_in_remaining':len(pending),'pending_names':pending,'implemented_or_core_owners':{n:claimed[n] for n in d if n in claimed},'all_local_owners':claimed},ensure_ascii=False,indent=2)+'\n')
print({'pending_in_remaining':len(pending),'mapped_original_declarations':sum(n in claimed for n in d),'extra_helpers':sum(n not in d for n in claimed)})
