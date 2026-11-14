"""Check the frozen public API, including binder names/order and implicitness.

Universe parameters are alpha-renamed by position and expression metadata is
discarded; compiler-generated binder hygiene scopes are erased. Explicit binder
names and all other elaborated type structure are retained. This deliberately
strict compatibility check complements the independent mathematical comparator.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

from verification_inputs import build_inputs, sha256

ROOT = Path(__file__).resolve().parents[1]
REFERENCE = ROOT / 'reference/public-api.json'
LEAN = r'''
import ConditionalGoldbach
import Lean
open Lean Elab Command

private partial def encodeType : Expr → Json
  | .mdata _ e => encodeType e
  | .bvar n => toJson ("bvar", n)
  | .sort u => toJson ("sort", reprStr u)
  | .const n us => toJson ("const", n.toString, us.map reprStr)
  | .app f x => toJson ("app", encodeType f, encodeType x)
  | .lam n t b i => toJson ("lam", n.eraseMacroScopes.toString, reprStr i, encodeType t, encodeType b)
  | .forallE n t b i => toJson ("forall", n.eraseMacroScopes.toString, reprStr i, encodeType t, encodeType b)
  | .letE n t v b nd => toJson ("let", n.eraseMacroScopes.toString, encodeType t, encodeType v, encodeType b, nd)
  | .lit l => toJson ("lit", reprStr l)
  | .proj n i e => toJson ("proj", n.toString, i, encodeType e)
  | .fvar n => toJson ("fvar", reprStr n)
  | .mvar n => toJson ("mvar", reprStr n)

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let names : Array String := __NAMES__
  let output ← liftIO <| IO.FS.Handle.mk __OUTPUT__ IO.FS.Mode.write
  for name in names do
    let some info := env.find? name.toName | throwError "Public API declaration missing: {name}"
    let levels := (List.range info.levelParams.length).map fun i =>
      Level.param (Name.mkSimple s!"apiUniverse{i}")
    let ty := info.type.instantiateLevelParams info.levelParams levels
    let row := Json.mkObj [
      ("name", toJson name), ("universe_arity", toJson info.levelParams.length),
      ("type", encodeType ty)]
    liftIO <| output.putStrLn row.compress
'''


def export_types(names):
    with tempfile.TemporaryDirectory(prefix='public-api-', dir=ROOT / '.lake') as directory:
        directory = Path(directory)
        output = directory / 'types.jsonl'
        source = LEAN.replace('__NAMES__', '#[' + ','.join(map(json.dumps, names)) + ']')
        source = source.replace('__OUTPUT__', json.dumps(str(output)))
        probe = directory / 'Check.lean'
        probe.write_text(source)
        result = subprocess.run(['lake', 'env', 'lean', '-DwarningAsError=true', str(probe)],
                                cwd=ROOT, env=os.environ | {'LEAN_NUM_THREADS': '2'},
                                capture_output=True, text=True)
        if result.returncode:
            raise RuntimeError(result.stdout + result.stderr)
        with output.open() as stream:
            for line in stream:
                yield json.loads(line)


def signatures(rows):
    return {row['name']: hashlib.sha256(json.dumps(
        [row['universe_arity'], row['type']], separators=(',', ':'),
        ensure_ascii=False).encode()).hexdigest() for row in rows}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, default=ROOT / 'verification')
    output_dir = parser.parse_args().output_dir.resolve()
    output_dir.mkdir(parents=True, exist_ok=True)
    before = build_inputs(ROOT)
    reference_hash = sha256(REFERENCE)
    baseline = json.loads(REFERENCE.read_text())
    current = signatures(export_types(baseline['names']))
    changed = [name for name in baseline['names'] if current[name] != baseline['signatures'][name]]
    if changed:
        raise ValueError('Public API types or binder interfaces changed: ' + ', '.join(changed))
    if build_inputs(ROOT) != before or sha256(REFERENCE) != reference_hash:
        raise ValueError('API check inputs changed during elaboration')
    output = dict(count=len(current), all_preserved=True, reference_sha256=reference_hash,
                  input_hashes=before, signatures=current)
    (output_dir / 'public-api.json').write_text(json.dumps(output, indent=2) + '\n')
    print(f'All {len(current)} frozen public declaration interfaces are preserved.')


if __name__ == '__main__':
    main()
