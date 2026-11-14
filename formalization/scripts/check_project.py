"""Incremental development checks, kept separate from full release evidence.

Lake rebuilds the changed modules and their dependents. All consumer boundaries,
reviewed definitions/types, frozen public interfaces and transitive axioms are
then checked. This command does not run or certify the independent comparator.
"""
import argparse
import datetime
import fcntl
import json
import os
from pathlib import Path
import subprocess
import tempfile
import time

from project_sources import ROOT
from verification_inputs import build_inputs, fingerprints, pinned_dependencies, sha256


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reuse-release', action='store_true',
                        help='Reuse complete release evidence only when every bound input is unchanged.')
    args = parser.parse_args()
    dependencies = pinned_dependencies(ROOT)
    if args.reuse_release:
        from update_verification import validate_current_evidence
        try:
            current = validate_current_evidence()
            published = json.loads((ROOT / 'verification.json').read_text())
            if any(published.get(key) != value for key, value in current.items()
                   if key != 'generated_at_utc'):
                raise ValueError('Published release record differs from the current evidence')
        except (ValueError, KeyError, FileNotFoundError) as error:
            print(f'Full release evidence is not current ({error}); running development checks.', flush=True)
        else:
            print('Unchanged full release evidence accepted, including the independent comparator.')
            return

    inputs = build_inputs(ROOT)
    tools = fingerprints(ROOT, [p.relative_to(ROOT) for p in (ROOT / 'scripts').glob('*.py')]
                         + [Path('scripts/ProofAudit.lean'), Path('scripts/entrypoints.json')])
    output = Path(tempfile.mkdtemp(prefix='development-check-', dir=ROOT / '.lake'))
    record = dict(scope='development', release_verified=False, input_hashes=inputs,
                  dependency_revisions=dependencies, tool_hashes=tools, runs=[], passed=False)

    def save():
        (output / 'result.json').write_text(json.dumps(record, indent=2) + '\n')

    commands = [('build', ['lake', '--wfail', 'build'])] + [
        (label, ['python3', 'scripts/' + script, '--output-dir', str(output)])
        for label, script in [('proof-policy', 'check_proof_policy.py'),
                              ('entrypoints', 'check_entrypoints.py'),
                              ('definitions', 'check_definitions.py'),
                              ('types', 'check_reviewed_types.py'),
                              ('public-api', 'check_public_api.py'),
                              ('axioms', 'audit_proofs.py')]]
    print(f'Development evidence: {output}', flush=True)
    save()
    for label, command in commands:
        start = time.monotonic()
        started = datetime.datetime.now(datetime.timezone.utc).isoformat()
        log = output / (label + '.log')
        with log.open('w') as stream:
            result = subprocess.run(command, cwd=ROOT, env=os.environ | {'LEAN_NUM_THREADS': '2'},
                                    stdout=stream, stderr=subprocess.STDOUT)
        row = dict(label=label, command=command, start_utc=started,
                   wall_seconds=time.monotonic() - start, exit_code=result.returncode,
                   log=log.name, log_sha256=sha256(log))
        record['runs'].append(row)
        save()
        print(f'{label}: exit {result.returncode}, {row["wall_seconds"]:.2f} s', flush=True)
        if result.returncode:
            raise SystemExit(f'{label} failed; see {log}')
    if build_inputs(ROOT) != inputs or pinned_dependencies(ROOT) != dependencies:
        raise ValueError('Inputs changed during development checks')
    if fingerprints(ROOT, tools) != tools:
        raise ValueError('Verification tools changed during development checks')
    record['passed'] = True
    save()
    print('Development checks passed. Full release verification remains a separate command.')


if __name__ == '__main__':
    (ROOT / '.lake').mkdir(exist_ok=True)
    with (ROOT / '.lake/verify-project.lock').open('a') as run_lock:
        fcntl.flock(run_lock, fcntl.LOCK_EX)
        with open('/tmp/conditional-goldbach-build.lock', 'a') as build_lock:
            fcntl.flock(build_lock, fcntl.LOCK_EX)
            main()
