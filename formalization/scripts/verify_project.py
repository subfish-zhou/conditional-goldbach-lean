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
from verification_inputs import (
    BUILD_COMMAND, DECLARATIONS, DEPENDENCY_OUTPUTS, PUBLICATION, build_inputs, fingerprints,
    pinned_dependencies, verification_tool_inputs,
)

ROOT = Path(__file__).resolve().parents[1]
LOCK = '/tmp/conditional-goldbach-build.lock'
RUN_LOCK = ROOT / '.lake/verify-project.lock'
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

    def run(label, command, log_path, *, audit_step=True, outputs=()):
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
        if completed.returncode == 0 and outputs:
            record['output_hashes'] = fingerprints(ROOT, outputs)
        if audit_step:
            runs.append(record)
            write_json(record_path, runs)
        else:
            if label == 'build':
                record['input_hashes'] = input_hashes
                record['dependency_revisions'] = dependency_revisions
                record['verification_tool_hashes'] = tool_hashes
                record['lean_num_threads'] = 2
                record['lock_file'] = LOCK
                jobs = re.search(r'Build completed successfully \((\d+) jobs\)', log_path.read_text())
                if jobs:
                    record['jobs'] = int(jobs[1])
            write_json(ROOT / f'verification/current-{label}.json', record)
        print(json.dumps({key: value for key, value in record.items() if key != 'input_hashes'}),
              flush=True)
        if completed.returncode:
            raise SystemExit(completed.returncode)
        return record

    # The comparator acquires this same lock itself; release it before invoking
    # run_comparator.py to avoid recursively locking through a child process.
    with open(LOCK, 'a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        input_hashes = build_inputs(ROOT)
        dependency_revisions = pinned_dependencies(ROOT)
        tool_hashes = verification_tool_inputs(ROOT)
        write_json(record_path, runs)
        run('build', list(BUILD_COMMAND), 'verification/current-build.log', audit_step=False)
        run('entrypoints', ['python3', 'scripts/check_entrypoints.py'],
            'verification/current-entrypoints.log', outputs=('verification/entrypoints.json',))
        for label, script, outputs in [
            ('proof-policy', 'check_proof_policy.py', ('verification/proof-policy.json',)),
            ('public-api', 'check_public_api.py', ('verification/public-api.json',)),
            ('definitions', 'check_definitions.py', ('reviewed-definitions.json',)),
            ('types', 'check_reviewed_types.py', ('reviewed-types.json',)),
            ('axioms', 'audit_proofs.py', ('proof-status.json', 'proof-status-raw.json')),
        ]:
            run(label, ['python3', 'scripts/' + script], f'verification/current-{label}.log',
                outputs=outputs)
        run('dependency-graph', ['lake', 'env', 'lean',
            DECLARATIONS + 'DeclarationAudit.lean'], DECLARATIONS + 'compile.log',
            outputs=DEPENDENCY_OUTPUTS['dependency-graph'])
        run('dependency-analysis', ['python3', DECLARATIONS + 'analyze.py'],
            DECLARATIONS + 'analyze-recheck.log', outputs=DEPENDENCY_OUTPUTS['dependency-analysis'])
        run('dependency-imports', ['python3', PUBLICATION + 'audit_imports.py'],
            PUBLICATION + 'imports-recheck.log', outputs=DEPENDENCY_OUTPUTS['dependency-imports'])
        sources = sorted(set([ROOT / 'ConditionalGoldbach.lean', *library_sources()]))
        if build_inputs(ROOT) != input_hashes:
            raise ValueError('Build inputs changed while verification was running')
        frozen = {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                  for path in sources}
        write_json(ROOT / AUDIT / 'frozen-source-hashes.json', frozen)
        run('comparator-prepare', ['python3', AUDIT + 'prepare_comparator.py'],
            'verification/current-comparator-prepare.log')

    run('comparator', ['python3', AUDIT + 'run_comparator.py'], 'verification/current-comparator.log',
        outputs=(AUDIT + 'comparator-result.json', AUDIT + 'independent-full-types.json'))
    if (build_inputs(ROOT) != input_hashes or pinned_dependencies(ROOT) != dependency_revisions
            or verification_tool_inputs(ROOT) != tool_hashes):
        raise ValueError('Build inputs changed during the comparator run')
    run('summary', ['python3', 'scripts/refresh_audit_summary.py'],
        'verification/current-summary.log', audit_step=False)
    run('dependency-records', ['python3', 'scripts/refresh_dependency_records.py'],
        'verification/current-dependency-records.log', audit_step=False)
    print('Build, proof audits, comparator and machine summaries passed. '
          'Next render and browser-check the English and Chinese reports, '
          'then run scripts/update_verification.py and scripts/package_verified.py.', flush=True)


if __name__ == '__main__':
    RUN_LOCK.parent.mkdir(exist_ok=True)
    with RUN_LOCK.open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        main()
