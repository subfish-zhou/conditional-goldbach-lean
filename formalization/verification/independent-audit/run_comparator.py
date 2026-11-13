"""Run the toolchain's actual, sandboxed comparator and rejection controls."""
from pathlib import Path
import datetime, fcntl, hashlib, json, os, subprocess, time

audit = Path(__file__).resolve().parent
project = audit.parents[1]
cwd = audit/'comparator-project'
lock = open('/tmp/conditional-goldbach-build.lock','a')
fcntl.flock(lock, fcntl.LOCK_EX)
env=os.environ.copy()
env['COMPARATOR_BWRAP']=str(audit/'bwrap_local_dependencies.py')
results = dict(tool='Lean 4.35.0 built-in lake comparator', sandbox='bwrap enabled; discovered dependency caches mounted read-only',
               sandbox_adapter_sha256=hashlib.sha256((audit/'bwrap_local_dependencies.py').read_bytes()).hexdigest(),
               permitted_axioms=['propext','Quot.sound','Classical.choice'], runs=[])

def run(name, args):
    started = datetime.datetime.now(datetime.timezone.utc).isoformat()
    t = time.perf_counter()
    path = audit/(name+'.log')
    with path.open('w') as log:
        p = subprocess.run(args,cwd=cwd,env=env,stdout=log,stderr=subprocess.STDOUT)
    r = dict(name=name,command=args,exit_code=p.returncode,start_utc=started,
             wall_seconds=time.perf_counter()-t,log=str(path.relative_to(audit)),
             log_sha256=hashlib.sha256(path.read_bytes()).hexdigest())
    results['runs'].append(r)
    (audit/'comparator-result.json').write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(r),flush=True)
    return p.returncode

code = run('independent-full-types-build',['lake','--no-cache','build','TexAuditComparator.CheckTypes'])
if code:
    raise SystemExit(code)
code = run('comparator',['lake','comparator','--config','comparator.json'])
for name in ['condition','quantifier','definition']:
    run('control-'+name,['lake','comparator','--config','control-'+name+'.json'])
frozen = json.loads((audit/'frozen-source-hashes.json').read_text())
results['library_sources_unchanged'] = all(hashlib.sha256((project/p).read_bytes()).hexdigest()==h
                                         for p,h in frozen.items())
manifest = json.loads((audit/'comparator-manifest.json').read_text())
results['reference_sources_unchanged'] = all(hashlib.sha256((audit/p).read_bytes()).hexdigest()==h
                                           for p,h in manifest['frozen_references'].items())
results['statement_count'] = manifest['statement_count']
results['definition_body_count'] = manifest['definition_body_count']
results['semantic_bridge_count'] = len(manifest['semantic_bridges'])
results['comparator_target_count'] = manifest['target_count']
type_rows=json.loads((audit/'independent-full-types.json').read_text())
results['all_independent_full_types_equal'] = (
    len(type_rows)==manifest['statement_count'] and
    all(r['full_type_definitionally_equal'] for r in type_rows) and
    {(r['expected'],r['actual']) for r in type_rows}==
    {(r['expected'],r['actual']) for r in manifest['statements']})
copies=[('sections-1-4/Expected.lean','Reference14.lean'),
        ('sections-5-7/Reference.lean','Reference57.lean'),
        ('appendices/Reference.lean','ReferenceAB.lean'),
        ('sections-1-4/Bridges.lean','Bridges14.lean'),
        ('sections-5-7/Bridges.lean','Bridges57.lean'),
        ('appendices/NumericCrossCheck.lean','NumericCrossCheck.lean')]
results['staged_references_match_frozen_sources']=all(
    hashlib.sha256((cwd/'TexAuditComparator'/target).read_bytes()).hexdigest()==manifest['frozen_references'][source]
    for source,target in copies)
results['accepted'] = code==0
results['negative_controls_rejected'] = all(r['exit_code']==1 and
    ('mismatch' in (audit/r['log']).read_text().lower() or
     'does not match' in (audit/r['log']).read_text().lower() or
     'do not match' in (audit/r['log']).read_text().lower())
    for r in results['runs'] if r['name'].startswith('control-'))
(audit/'comparator-result.json').write_text(json.dumps(results,indent=2)+'\n')
fcntl.flock(lock, fcntl.LOCK_UN)
print(json.dumps({k:v for k,v in results.items() if k!='runs'},indent=2),flush=True)
raise SystemExit(0 if results['accepted'] and results['negative_controls_rejected'] and
                 results['library_sources_unchanged'] and results['reference_sources_unchanged'] and
                 results['all_independent_full_types_equal'] and results['staged_references_match_frozen_sources'] else 1)
