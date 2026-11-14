"""Compile one-import consumers and enforce their import boundaries and budgets.

Run after `lake --wfail build`. The main verification runner also runs this check.
The compiled environment is the authority for the imported-module inventory.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess
import tempfile

from verification_inputs import build_inputs, manifest_revisions

ROOT = Path(__file__).resolve().parents[1]
POLICY = ROOT / 'scripts/entrypoints.json'
OUTPUT = ROOT / 'verification/entrypoints.json'


def enforce(entry, modules):
    """Keep consumer boundaries independent of the source-graph audit."""
    counts = {
        'total': len(modules),
        'local': sum(n == 'ConditionalGoldbach' or n.startswith('ConditionalGoldbach.')
                     for n in modules),
        'mathlib': sum(n.startswith('Mathlib.') for n in modules),
        'goldbach': sum(n.split('.')[0] in
                        ('MathlibNt', 'AnalyticNumberTheory', 'PrimeNumberTheoremAnd', 'Goldbach')
                        for n in modules),
    }
    if entry['module'] not in modules:
        raise ValueError(f"Consumer did not load {entry['module']}")
    for prefix in entry['forbid_prefixes']:
        bad = sorted(n for n in modules if n == prefix or n.startswith(prefix + '.'))
        if bad:
            raise ValueError(f"{entry['module']} imported forbidden modules: {bad}")
    if 'allowed_proof_modules' in entry:
        unexpected = {n for n in modules if n.startswith('ConditionalGoldbach.Proofs.')} - set(
            entry['allowed_proof_modules'])
        if unexpected:
            raise ValueError(f"{entry['module']} imported unexpected proof modules: {sorted(unexpected)}")
    for metric, limit in entry['max_imports'].items():
        if counts[metric] > limit:
            raise ValueError(f"{entry['module']}: {metric} imports {counts[metric]} exceed {limit}")
    return counts


def main():
    argparse.ArgumentParser(description=__doc__).parse_args()
    policy_bytes = POLICY.read_bytes()
    entries = json.loads(policy_bytes)['entries']
    inputs = build_inputs(ROOT)
    rows = []
    with tempfile.TemporaryDirectory(prefix='entrypoints-', dir=ROOT / '.lake') as tmp:
        tmp = Path(tmp)
        for entry in entries:
            output = tmp / 'modules.json'
            output.unlink(missing_ok=True)
            source = 'import ' + entry['module'] + '\n\n'
            source += '\n'.join('#check @' + n for n in entry['declarations']) + '\n\n'
            source += '''open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.header.moduleNames.map Name.toString
  liftIO <| IO.FS.writeFile ''' + json.dumps(str(output)) + ''' (toJson names).pretty
'''
            probe = tmp / 'Consumer.lean'
            probe.write_text(source)
            command = ['lake', 'env', 'lean', '-DwarningAsError=true', str(probe)]
            result = subprocess.run(command, cwd=ROOT, env=os.environ | {'LEAN_NUM_THREADS': '2'},
                                    capture_output=True, text=True)
            if result.returncode:
                raise RuntimeError(f"{entry['module']} consumer failed:\n{result.stdout}{result.stderr}")
            modules = set(json.loads(output.read_text()))
            counts = enforce(entry, modules)
            rows.append(dict(module=entry['module'], declarations=entry['declarations'],
                             counts=counts, imported_modules=sorted(modules),
                             consumer_source=source.replace(str(output), '<temporary modules.json>'),
                             diagnostics=result.stdout + result.stderr))
            print(entry['module'], counts, flush=True)
    if build_inputs(ROOT) != inputs or POLICY.read_bytes() != policy_bytes:
        raise RuntimeError('Build inputs or entrypoint policy changed during the check')
    OUTPUT.write_text(json.dumps(dict(
        policy_sha256=hashlib.sha256(policy_bytes).hexdigest(), input_hashes=inputs,
        dependency_revisions=manifest_revisions(ROOT),
        counting='Compiled imported modules, including the selected entrypoint. '
                 'Goldbach counts its four mathematical namespace roots; annotation tools are separate.',
        entries=rows), indent=2) + '\n')
    print('All isolated consumers, import boundaries and budgets passed.')


if __name__ == '__main__':
    main()
