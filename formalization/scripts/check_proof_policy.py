"""Keep production elaboration options local and every source reachable."""
import argparse
import json
from pathlib import Path
import re

from project_sources import ROOT, library_sources


def violations(source):
    """Performance exceptions must be scoped with `in`, never file-wide."""
    pattern = re.compile(r'^\s*set_option (maxHeartbeats|maxRecDepth|'
                         r'backward\.isDefEq\.respectTransparency)\b')
    return [(i, line.strip()) for i, line in enumerate(source.splitlines(), 1)
            if pattern.match(line) and not line.strip().endswith(' in')]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, default=ROOT / 'verification')
    output = parser.parse_args().output_dir.resolve()
    output.mkdir(parents=True, exist_ok=True)
    sources = [ROOT / 'ConditionalGoldbach.lean', *library_sources()]
    on_disk = {ROOT / 'ConditionalGoldbach.lean',
               *(ROOT / 'ConditionalGoldbach').rglob('*.lean')}
    if set(sources) != on_disk:
        raise ValueError('Production sources outside the root import closure: ' +
                         ', '.join(str(p.relative_to(ROOT)) for p in on_disk - set(sources)))
    errors = [(str(p.relative_to(ROOT)), line, option)
              for p in sources for line, option in violations(p.read_text())]
    if errors:
        raise ValueError('Unscoped production elaboration options: ' + repr(errors))
    result = dict(production_files=len(sources), no_global_overrides=True, all_sources_reachable=True)
    (output / 'proof-policy.json').write_text(json.dumps(result, indent=2) + '\n')
    print(f'Proof policy passed for {len(sources)} production modules.')


if __name__ == '__main__':
    main()
