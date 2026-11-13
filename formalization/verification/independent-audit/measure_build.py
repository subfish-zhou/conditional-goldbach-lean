"""Measure a build after acquiring the shared build lock; preserve proof sources."""
from pathlib import Path
import datetime, fcntl, json, os, platform, resource, shutil, subprocess, sys, time

audit = Path(__file__).resolve().parent
project = audit.parents[1]
mode = sys.argv[1]
assert mode in ('warm', 'project-clean')
cwd = project if mode == 'warm' else audit / 'benchmark-project'
if mode == 'project-clean':
    if (cwd/'.lake/build').exists() and any((cwd/'.lake/build').rglob('*.olean')):
        raise SystemExit('Refusing to label a cached build as clean. Preserve/move the previous benchmark-project directory before repeating this measurement.')
    sys.path.insert(0,str(project/'scripts'))
    from project_sources import library_sources
    for source in library_sources()+[project/'LiLiuGoldbach.lean',project/'lakefile.toml',project/'lake-manifest.json',project/'lean-toolchain']:
        target=cwd/source.relative_to(project)
        target.parent.mkdir(parents=True,exist_ok=True)
        shutil.copy2(source,target)
    (cwd/'.lake').mkdir(exist_ok=True)
    if not (cwd/'.lake/packages').exists():
        (cwd/'.lake/packages').symlink_to(project/'.lake/packages',target_is_directory=True)
env = os.environ.copy()
if mode == 'project-clean':
    # Limit Lake's runtime worker pool on the shared 8-CPU, 32-GiB host.
    env['LEAN_NUM_THREADS'] = '2'
lock = open('/tmp/liliu-build.lock', 'a')
queued = time.perf_counter()
fcntl.flock(lock, fcntl.LOCK_EX)
queue_seconds = time.perf_counter() - queued
started = datetime.datetime.now(datetime.timezone.utc)
before = resource.getrusage(resource.RUSAGE_CHILDREN)
t = time.perf_counter()
with (audit / f'build-{mode}.log').open('w') as log:
    result = subprocess.run(['lake', '--no-cache', 'build'], cwd=cwd, env=env,
                            stdout=log, stderr=subprocess.STDOUT)
elapsed = time.perf_counter() - t
after = resource.getrusage(resource.RUSAGE_CHILDREN)
fcntl.flock(lock, fcntl.LOCK_UN)
record = dict(mode=mode, command=['lake', '--no-cache', 'build'], cwd=str(cwd),
              start_utc=started.isoformat(), wall_seconds=elapsed,
              user_cpu_seconds=after.ru_utime-before.ru_utime,
              system_cpu_seconds=after.ru_stime-before.ru_stime,
              largest_child_maxrss_kib=after.ru_maxrss,
              queue_seconds_excluded=queue_seconds, exit_code=result.returncode,
              cpu_count=os.cpu_count(), machine=platform.machine(),
              lean_num_threads=env.get('LEAN_NUM_THREADS', 'default'),
              dependency_cache='existing Mathlib and goldbach build artifacts reused',
              source_cache='existing' if mode == 'warm' else 'empty project build directory')
(audit / f'build-{mode}.json').write_text(json.dumps(record, indent=2)+'\n')
print(json.dumps(record, indent=2), flush=True)
sys.exit(result.returncode)
