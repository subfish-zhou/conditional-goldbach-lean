"""Validate portable package configuration without rewriting historical audit logs."""
from pathlib import Path
import datetime, fcntl, hashlib, json, os, subprocess, time

here=Path(__file__).resolve().parent
project=here.parents[1]
audit=project/'verification/independent-audit'
cmp=audit/'comparator-project'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
env=os.environ.copy()
env['COMPARATOR_BWRAP']=str(audit/'bwrap_local_dependencies.py')
record={'scope':'Portable Git dependency configuration, full independent type assignment, comparator transport and rejection controls; the previous 218-target full kernel audit is preserved separately.',
        'time_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(), 'steps':[]}

def run(label,command,want=0):
    t=time.perf_counter(); log=here/(label+'.log')
    with log.open('w') as output:
        result=subprocess.run(command,cwd=cmp,env=env,stdout=output,stderr=subprocess.STDOUT)
    item={'label':label,'command':command,'exit_code':result.returncode,
          'expected_exit_code':want,'wall_seconds':time.perf_counter()-t,'log':log.name,'log_sha256':sha(log)}
    if want==1:
        assert 'do not match' in log.read_text() or 'does not match' in log.read_text(), log
    assert result.returncode==want,item
    record['steps'].append(item);print(json.dumps(item),flush=True)

with open('/tmp/liliu-build.lock','a') as lock:
    fcntl.flock(lock,fcntl.LOCK_EX)
    run('portable-comparator-build',['lake','build','TexAuditComparator.CheckTypes','TexAuditComparator.Solution'])
    run('portable-comparator-smoke',['lake','comparator','--config','../../publication/comparator-smoke.json'])
    for kind in ['condition','quantifier','definition']:
        run('portable-control-'+kind,['lake','comparator','--config','control-'+kind+'.json'],1)

types=json.loads((audit/'independent-full-types.json').read_text())
assert len(types)==103 and all(row['full_type_definitionally_equal'] for row in types)
frozen=json.loads((audit/'frozen-source-hashes.json').read_text())
assert all(sha(project/p)==h for p,h in frozen.items())
record['frozen_mathematical_source_files_unchanged']=len(frozen)
record['independent_full_types_passed']=len(types)
record['main_build_passed']='Build completed successfully' in (here/'build.log').read_text()
assert record['main_build_passed']
record['main_build_log_sha256']=sha(here/'build.log')
record['configuration_hashes']={str(p.relative_to(project)):sha(p) for p in [project/'lakefile.toml',project/'lake-manifest.json',cmp/'lakefile.toml',cmp/'lake-manifest.json',audit/'bwrap_local_dependencies.py']}
record['passed']=True
(here/'verification.json').write_text(json.dumps(record,indent=2)+'\n')
print('Portable publication validation passed.',flush=True)
