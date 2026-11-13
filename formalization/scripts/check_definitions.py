"""Check that all 171 reviewed definition bodies remain textually unchanged.
Whitespace and comments between declarations are ignored; the actual declaration
text, including hypotheses and body, must match the reviewed snapshot.
"""
from pathlib import Path
import re,json,hashlib
ROOT=Path(__file__).resolve().parents[1]
base=json.loads((ROOT/'reference/declarations.json').read_text())
source_paths=[ROOT/'LiLiuGoldbach/BaseDefinitions.lean',ROOT/'LiLiuGoldbach/Definitions.lean']
lines=[]
for source in source_paths:
 if source.exists():lines.extend(source.read_text().splitlines()+['end'])
command=re.compile(r'^(?:(?:noncomputable|private|protected|local)\s+)*(?:def|abbrev|theorem|lemma|structure|instance|namespace|end|open|attribute|set_option|section|import)\b')
current={}
for i,l in enumerate(lines):
 m=re.match(r'^(def|abbrev|structure)\s+(\w+)',l)
 if not m:continue
 j=i+1
 while j<len(lines) and not command.match(lines[j]):j+=1
 c=lines[i:j]
 while c and not c[-1].strip():c.pop()
 while c and (c[-1].startswith('--') or c[-1].rstrip().endswith('-/')):
  if c[-1].startswith('--'):c.pop()
  else:
   k=next((k for k in range(len(c)-1,0,-1) if c[k].lstrip().startswith('/-')),None)
   if k is None:break
   c=c[:k]
  while c and not c[-1].strip():c.pop()
 current[m[2]]='\n'.join(c)
normal=lambda s:re.sub(r'\s+','',s)
rows=[]
for n,r in base.items():
 if r['kind']=='theorem':continue
 assert n in current,n
 equal=normal(r['code'])==normal(current[n]);assert equal,n
 rows.append({'name':'LiLiuGoldbach16.'+n,'reviewed_definition_preserved':equal,'normalized_sha256':hashlib.sha256(normal(current[n]).encode()).hexdigest()})
assert len(rows)==171
(ROOT/'reviewed-definitions.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
print('All 171 reviewed definition bodies are unchanged (ignoring whitespace).')
