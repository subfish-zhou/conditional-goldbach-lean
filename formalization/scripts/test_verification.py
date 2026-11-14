"""Check publication validation with copied and deliberately modified evidence."""
import json
import os
import shutil
from pathlib import Path
import tempfile

import update_verification as verifier
from check_entrypoints import enforce

original = verifier.ROOT
repo = original.parent
release = json.loads((original / 'verification.json').read_text())
with tempfile.TemporaryDirectory(prefix='quality-evidence-') as temporary:
    copy = Path(temporary)
    items = {original / row['file'] for row in release['source_files'] + release['evidence_files']}
    items.add(repo / 'outputs/formalization-preparation/conditional-goldbach.tex')
    for path in items:
        destination = copy / path.relative_to(repo)
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, destination)
        os.utime(destination, (0, 0))
    verifier.ROOT = copy / 'formalization'
    assert verifier.validate_current_evidence()['schema_version'] == 3
    print('Copied release with epoch mtimes: accepted')

    def reject(relative_path, edit, expected_message):
        path = verifier.ROOT / relative_path
        before = path.read_bytes()
        try:
            edit(path)
            try:
                verifier.validate_current_evidence()
            except ValueError as error:
                assert expected_message in str(error), str(error)
                print(f'{relative_path}: {error}')
            else:
                raise AssertionError(f'Modified release artifact accepted: {relative_path}')
        finally:
            path.write_bytes(before)

    def replace_target(path):
        config = json.loads(path.read_text())
        config['theorem_names'][0] = 'TexAudit14.unrelated_quality_probe'
        path.write_text(json.dumps(config))

    def append_byte(path):
        path.write_bytes(path.read_bytes() + b'\n')

    reject(verifier.AUDIT + 'comparator-project/comparator.json',
           replace_target, 'Comparator target inventory differs')
    reject(verifier.AUDIT + 'comparator-project/control-condition.json',
           append_byte, 'Comparator inputs changed since the run')
    reject('reviewed-types.json', append_byte, 'Audit output changed since the run')
    reject('scripts/entrypoints.json', append_byte, 'Entrypoint policy changed since the run')
    reject('verification/entrypoints.json', append_byte,
           'Audit output changed since the run: entrypoints')
    reject(verifier.PUBLICATION + 'dependencies-imports.json', append_byte,
           'Audit output changed since the run: dependency-imports')
    reject('ConditionalGoldbach/Proofs/Main.lean', append_byte, 'Build inputs differ')
    assert verifier.validate_current_evidence()['comparator']['comparator_target_count'] == 218

    entries = json.loads((verifier.ROOT / 'scripts/entrypoints.json').read_text())['entries']
    policy = {entry['module']: entry for entry in entries}
    main = policy['ConditionalGoldbach.Proofs.Main']
    definitions = policy['ConditionalGoldbach.Definitions']
    for entry, modules, reason in [
        (main, {main['module'], 'ConditionalGoldbach.Proofs.TotientLogLog'}, 'forbidden'),
        (definitions, {definitions['module'], main['module']}, 'unexpected proof'),
        (main, {main['module']} | {f'Mathlib.Probe{i}' for i in
                                  range(main['max_imports']['mathlib'] + 1)}, 'exceed'),
    ]:
        try:
            enforce(entry, modules)
        except ValueError as error:
            assert reason in str(error), str(error)
            print('Entrypoint regression rejected:', reason)
        else:
            raise AssertionError('Entrypoint regression accepted: ' + reason)
