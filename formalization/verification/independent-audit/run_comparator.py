"""Run Lean's sandboxed comparator and record the inputs it checked."""
import datetime
import fcntl
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time

AUDIT = Path(__file__).resolve().parent
PROJECT = AUDIT.parents[1]
STAGED = AUDIT / 'comparator-project'
sys.path.insert(0, str(PROJECT / 'scripts'))
from verification_inputs import (  # noqa: E402
    COMPARATOR_AXIOMS, CONTROLS, FULL_TYPE_CHECK, build_inputs, comparator_inputs, comparator_targets,
    pinned_dependencies, read_json, sha256, verification_tool_inputs,
)


def main():
    manifest = read_json(AUDIT / 'comparator-manifest.json')
    config = read_json(STAGED / 'comparator.json')
    targets = comparator_targets(manifest, config)
    inputs = comparator_inputs(PROJECT, AUDIT, manifest)
    build_path = PROJECT / 'verification/current-build.json'
    build_hash = sha256(build_path)
    build = read_json(build_path)
    current_build_inputs = build_inputs(PROJECT)
    frozen = {name: value for name, value in current_build_inputs.items()
              if name.startswith('ConditionalGoldbach') and name.endswith('.lean')}
    dependencies = pinned_dependencies(PROJECT)
    if (build['exit_code'] != 0 or build['input_hashes'] != current_build_inputs
            or build['dependency_revisions'] != dependencies
            or frozen != read_json(AUDIT / 'frozen-source-hashes.json')
            or build.get('verification_tool_hashes') != verification_tool_inputs(PROJECT)):
        raise ValueError('Comparator inputs differ from the recorded build')
    if any(sha256(AUDIT / name) != expected
           for name, expected in manifest['frozen_references'].items()):
        raise ValueError('Independent comparator references changed after preparation')

    env = os.environ.copy()
    env['COMPARATOR_BWRAP'] = str(AUDIT / 'bwrap_local_dependencies.py')
    runs = []

    def run(name, command):
        started = datetime.datetime.now(datetime.timezone.utc).isoformat()
        start = time.monotonic()
        log = AUDIT / (name + '.log')
        phases = AUDIT / (name + '-phases.jsonl')
        phases.unlink(missing_ok=True)
        # Lean invokes COMPARATOR_BWRAP via `env -i`, so a trace environment
        # variable cannot reach the adapter. A temporary executable passes the
        # host-side trace path as an argument without altering the sandbox env.
        with tempfile.TemporaryDirectory(prefix='comparator-trace-', dir=PROJECT / '.lake') as tmp:
            launcher = Path(tmp) / 'bwrap-trace'
            adapter = str(AUDIT / 'bwrap_local_dependencies.py')
            launcher.write_text('#!/usr/bin/python3\nimport os, sys\n'
                + f'os.execv({adapter!r}, [{adapter!r}, "--trace-file", {str(phases)!r}, *sys.argv[1:]])\n')
            launcher.chmod(0o700)
            with log.open('w') as stream:
                result = subprocess.run(command, cwd=STAGED,
                                        env=env | {'COMPARATOR_BWRAP': str(launcher)},
                                        stdout=stream, stderr=subprocess.STDOUT)
        if name != 'independent-full-types-build' and (not phases.exists() or phases.stat().st_size == 0):
            raise ValueError('Comparator sandbox phase log was not produced: ' + name)
        row = dict(name=name, command=command, exit_code=result.returncode, start_utc=started,
                   wall_seconds=time.monotonic() - start, log=log.name, log_sha256=sha256(log))
        if phases.exists():
            row['sandbox_phases'] = [json.loads(line) for line in phases.read_text().splitlines()]
            row['phase_log'] = phases.name
            row['phase_log_sha256'] = sha256(phases)
        runs.append(row)
        print(json.dumps({key: value for key, value in row.items() if key != 'sandbox_phases'}), flush=True)
        return result.returncode

    type_file = AUDIT / 'independent-full-types.json'
    type_file.unlink(missing_ok=True)
    # lake lean builds the imports and always elaborates this file. A cached
    # lake build would skip the run_cmd that writes the comparison results.
    code = run('independent-full-types-build', list(FULL_TYPE_CHECK))
    if code:
        return code
    type_hash = sha256(type_file)
    types = read_json(type_file)
    expected = {(row['expected'], row['actual']) for row in manifest['statements']}
    all_types_equal = (
        len(types) == len(expected) and all(row['full_type_definitionally_equal'] is True for row in types)
        and {(row['expected'], row['actual']) for row in types} == expected
    )
    if not all_types_equal:
        raise ValueError('Full-type comparison differs from the independent manifest')

    code = run('comparator', ['lake', 'comparator', '--config', 'comparator.json'])
    for name in CONTROLS:
        run('control-' + name, ['lake', 'comparator', '--config', f'control-{name}.json'])

    copies = {
        'sections-1-4/Expected.lean': 'Reference14.lean',
        'sections-5-7/Reference.lean': 'Reference57.lean',
        'appendices/Reference.lean': 'ReferenceAB.lean',
        'sections-1-4/Bridges.lean': 'Bridges14.lean',
        'sections-5-7/Bridges.lean': 'Bridges57.lean',
        'appendices/NumericCrossCheck.lean': 'NumericCrossCheck.lean',
    }
    staged_match = all(sha256(STAGED / 'TexAuditComparator' / target)
                       == manifest['frozen_references'][source] for source, target in copies.items())
    rejected = all(
        row['exit_code'] == 1 and any(
            phrase in (AUDIT / row['log']).read_text().lower()
            for phrase in ('mismatch', 'does not match', 'do not match'))
        for row in runs if row['name'].startswith('control-')
    )
    if (inputs != comparator_inputs(PROJECT, AUDIT, manifest) or type_hash != sha256(type_file)
            or build_hash != sha256(build_path) or dependencies != pinned_dependencies(PROJECT)):
        raise ValueError('Comparator inputs or full-type results changed during verification')
    result = dict(
        tool='Lean 4.35.0 built-in lake comparator',
        sandbox='bwrap enabled; discovered dependency caches mounted read-only',
        sandbox_adapter_sha256=sha256(AUDIT / 'bwrap_local_dependencies.py'),
        permitted_axioms=sorted(COMPARATOR_AXIOMS), runs=runs, input_hashes=inputs,
        build_sha256=build_hash,
        independent_full_types_sha256=type_hash, library_sources_unchanged=True,
        reference_sources_unchanged=True, staged_references_match_frozen_sources=staged_match,
        statement_count=len(types), definition_body_count=len(manifest['definitions']),
        semantic_bridge_count=len(manifest['semantic_bridges']), comparator_target_count=len(targets),
        all_independent_full_types_equal=True, accepted=code == 0, negative_controls_rejected=rejected,
    )
    (AUDIT / 'comparator-result.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({key: value for key, value in result.items() if key != 'input_hashes'},
                     indent=2), flush=True)
    return 0 if code == 0 and rejected and staged_match else 1


if __name__ == '__main__':
    with open('/tmp/conditional-goldbach-build.lock', 'a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        raise SystemExit(main())
