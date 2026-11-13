"""Reproduce the current build, proof audits, comparator and machine summaries."""
from pathlib import Path
import argparse
import datetime
import fcntl
import hashlib
import json
import os
import re
import subprocess
import time

from project_sources import library_sources

ROOT = Path(__file__).resolve().parents[1]
LOCK = '/tmp/conditional-goldbach-build.lock'
AUDIT = 'verification/independent-audit/'


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + '\n')


def main():
    parser = argparse.ArgumentParser(
        description='Build the Lean project, check definitions/types/axioms and dependency records, '
                    'run the complete comparator with rejection controls, and refresh machine summaries.',
        epilog='Requires the pinned Lean/Lake environment and Linux bubblewrap. '
               'Uses two Lean worker threads and the shared project build lock. '
               'Render and browser-check both report languages afterwards, then run '
               'update_verification.py and package_verified.py.')
    parser.parse_args()
    env = os.environ.copy()
    env['LEAN_NUM_THREADS'] = '2'
    runs = []
    record_path = ROOT / 'verification/current-audits.json'

    def run(label, command, log_path, *, audit_step=True):
        log_path = ROOT / log_path
        log_path.parent.mkdir(parents=True, exist_ok=True)
        started = datetime.datetime.now(datetime.timezone.utc).isoformat()
        before = time.monotonic()
        with log_path.open('w') as output:
            completed = subprocess.run(command, cwd=ROOT, env=env, stdout=output,
                                       stderr=subprocess.STDOUT)
        record = dict(
            label=label, command=command, exit_code=completed.returncode,
            start_utc=started, wall_seconds=time.monotonic() - before,
            log=str(log_path.relative_to(ROOT)),
            log_sha256=hashlib.sha256(log_path.read_bytes()).hexdigest())
        if audit_step:
            runs.append(record)
            write_json(record_path, runs)
        else:
            if label == 'build':
                record['lean_num_threads'] = 2
                record['lock_file'] = LOCK
                jobs = re.search(r'Build completed successfully \((\d+) jobs\)', log_path.read_text())
                if jobs:
                    record['jobs'] = int(jobs[1])
            write_json(ROOT / f'verification/current-{label}.json', record)
        print(json.dumps(record), flush=True)
        if completed.returncode:
            raise SystemExit(completed.returncode)
        return record

    # The comparator acquires this same lock itself; release it before invoking
    # run_comparator.py to avoid recursively locking through a child process.
    with open(LOCK, 'a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        write_json(record_path, runs)
        run('build', ['lake', 'build'], 'verification/current-build.log', audit_step=False)
        for label, script in [('definitions', 'check_definitions.py'),
                              ('types', 'check_reviewed_types.py'), ('axioms', 'audit_proofs.py')]:
            run(label, ['python3', 'scripts/' + script], f'verification/current-{label}.log')
        run('dependency-graph', ['lake', 'env', 'lean',
            'verification/publication/declaration-audit/DeclarationAudit.lean'],
            'verification/publication/declaration-audit/compile.log')
        run('dependency-analysis', ['python3', 'verification/publication/declaration-audit/analyze.py'],
            'verification/publication/declaration-audit/analyze-recheck.log')
        run('dependency-imports', ['python3', 'verification/publication/audit_imports.py'],
            'verification/publication/imports-recheck.log')
        sources = sorted(set([ROOT / 'ConditionalGoldbach.lean', *library_sources()]))
        if len(sources) != 254:
            raise ValueError(f'Expected 254 files in the project import closure, found {len(sources)}')
        frozen = {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                  for path in sources}
        write_json(ROOT / AUDIT / 'frozen-source-hashes.json', frozen)
        run('comparator-prepare', ['python3', AUDIT + 'prepare_comparator.py'],
            'verification/current-comparator-prepare.log')

    run('comparator', ['python3', AUDIT + 'run_comparator.py'], 'verification/current-comparator.log')
    run('summary', ['python3', 'scripts/refresh_audit_summary.py'],
        'verification/current-summary.log', audit_step=False)
    run('dependency-records', ['python3', 'scripts/refresh_dependency_records.py'],
        'verification/current-dependency-records.log', audit_step=False)
    print('Build, proof audits, comparator and machine summaries passed. '
          'Next render and browser-check the English and Chinese reports, '
          'then run scripts/update_verification.py and scripts/package_verified.py.', flush=True)


if __name__ == '__main__':
    main()
