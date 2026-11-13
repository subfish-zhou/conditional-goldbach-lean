"""Refresh dependency and section records from successful current verification runs."""
from pathlib import Path
import json,hashlib,datetime,collections
root=Path(__file__).resolve().parents[1];pub=root/'verification/publication';audit=root/'verification/independent-audit';dec=pub/'declaration-audit'
read=lambda p:json.loads(p.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
write=lambda p,d:p.write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
runs=read(root/'verification/current-audits.json');build=read(root/'verification/current-build.json');comp=read(audit/'comparator-result.json');manifest=read(audit/'comparator-manifest.json')
assert comp['accepted'] and comp['library_sources_unchanged'] and comp['reference_sources_unchanged'] and comp['all_independent_full_types_equal'] and comp['negative_controls_rejected']
for run in runs:
 assert run['exit_code']==0 and sha(root/run['log'])==run['log_sha256'],run['label']
frozen=read(audit/'frozen-source-hashes.json')
assert all(sha(root/p)==h for p,h in frozen.items())
write(dec/'source-hashes.json',frozen)
graph=read(dec/'declaration-graph.json');assert not graph['missing']
metadata=read(dec/'metadata.json')
metadata.update(graph_sha256=sha(dec/'declaration-graph.json'),collected_at_utc=next(r['start_utc'] for r in runs if r['label']=='dependency-graph'),missing_constants=graph['missing'],imported_module_count=len(graph['imported_modules']))
write(dec/'metadata.json',metadata)
nodes={r['name']:r for r in graph['declarations']}
mertens=[]
for name in read(dec/'reviewed-names.json'):
 seen=set();todo=[name];uses=False
 while todo:
  n=todo.pop()
  if n in seen:continue
  seen.add(n);r=nodes[n]
  if r['module']=='MathlibNt.SieveTheory.Arithmetic.MertensTheorem':uses=True;break
  todo.extend(r['type_refs']+r['value_refs']+r['constructor_refs'])
 if uses:mertens.append(name)
write(dec/'reviewed-requiring-mertens.json',sorted(mertens))
imp=read(pub/'dependencies-imports.json');assert not imp['unresolved_imports'];assert imp['compiled_environment_crosscheck']['exact_match']
configs=['lakefile.toml','lake-manifest.json','verification/independent-audit/comparator-project/lakefile.toml','verification/independent-audit/comparator-project/lake-manifest.json','verification/independent-audit/bwrap_local_dependencies.py']
write(pub/'verification.json',dict(scope='Current renamed library, complete independent comparator, and external declaration/import dependencies.',time_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),build=build,dependency_audits=[r for r in runs if r['label'].startswith('dependency-')],comparator_record='../independent-audit/comparator-result.json',comparator_sha256=sha(audit/'comparator-result.json'),comparator_targets=comp['comparator_target_count'],independent_full_types_passed=comp['statement_count'],frozen_mathematical_source_files_unchanged=len(frozen),configuration_hashes={p:sha(root/p) for p in configs},passed=True))
for group,name in [('sections-1-4','local-verification.json'),('sections-5-7','verification.json'),('appendices','verification.json')]:
 rows=[r for r in manifest['statements'] if r['audit_group']==group];defs=[r for r in manifest['definitions'] if r['audit_group']==group]
 record=dict(scope=group,frozen_reference_base='..',independent_full_types=len(rows),definition_body_comparisons=len(defs),source_tex_sha256=sha(root.parent/'outputs/formalization-preparation/conditional-goldbach.tex'),comparator_record='../comparator-result.json',comparator_sha256=sha(audit/'comparator-result.json'),current_comparator_accepted=True,all_independent_full_types_equal=True,frozen_reference_files={p:h for p,h in manifest['frozen_references'].items() if p.startswith(group+'/')})
 write(audit/group/name,record)
print(json.dumps({'refreshed_publication_and_group_records':True,'reviewed_using_mertens':mertens,'external_modules':len(imp['goldbach_package_modules'])}))
