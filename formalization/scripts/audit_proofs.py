"""Audit all project-owned Lean constants and locate public declarations."""
import hashlib
import json
import subprocess

from project_sources import ROOT, library_sources
from verification_inputs import COMPARATOR_AXIOMS

STANDARD_AXIOMS = COMPARATOR_AXIOMS
THEOREM_KINDS = {'theorem', 'lemma'}
THEOREM_STATUSES = ('kernel_closed', 'proof_written_dependencies_pending', 'pending_direct_sorry')


def source_kind(row, lines):
    """Identify declarations written in the source using Lean's selection range."""
    span = row['source_range']
    if row['private'] or not span or span['name_line'] != span['name_end_line']:
        return None
    name = lines[span['name_line'] - 1][span['name_column']:span['name_end_column']]
    declaration = row['name']
    short = name.removeprefix('_root_.')
    if not short or not (declaration == short or declaration.endswith('.' + short)):
        return None
    prefix = lines[span['name_line'] - 1][:span['name_column']]
    if row['kind'] == 'theorem' and prefix.rstrip().endswith('lemma'):
        return 'lemma'
    return row['kind'] if row['kind'] != 'generated' else None


def counts(rows):
    return {key: sum(row['status'] == key for row in rows) for key in THEOREM_STATUSES}


def main():
    baseline = json.loads((ROOT / 'reference/declarations.json').read_text())
    raw = ROOT / 'proof-status-raw.json'
    raw.unlink(missing_ok=True)
    with (ROOT / 'audit.log').open('w') as log:
        result = subprocess.run(['lake', 'env', 'lean', 'scripts/ProofAudit.lean'], cwd=ROOT,
                                stdout=log, stderr=subprocess.STDOUT)
    if result.returncode:
        raise SystemExit('Audit elaboration failed. See audit.log.')
    records = json.loads(raw.read_text())
    by_name = {row['name']: row for row in records}
    source_paths = library_sources()
    sources = {str(path.relative_to(ROOT)): path.read_text().splitlines() for path in source_paths}
    sources['ConditionalGoldbach.lean'] = (ROOT / 'ConditionalGoldbach.lean').read_text().splitlines()
    allowed = STANDARD_AXIOMS | {'sorryAx'}
    unusual = sorted({a for row in records for a in row['axioms']} - allowed)
    admissions = {row['name'] for row in records
                  if row['contains_sorry_directly'] or 'sorryAx' in row['axioms']}
    stubs = {row['name'] for row in records if row['contains_sorry_directly']}

    def pending_dependencies(name):
        seen = set()
        pending = [name]
        while pending:
            current = pending.pop()
            if current in seen or current not in by_name:
                continue
            seen.add(current)
            row = by_name[current]
            pending.extend(row['type_constants'] + row['value_constants'])
        return sorted(seen & stubs)

    declarations = []
    for row in records:
        file = row['module'].replace('.', '/') + '.lean'
        kind = source_kind(row, sources[file])
        if kind is None:
            continue
        span = row['source_range']
        name = row['name']
        closed = name not in admissions
        if kind in THEOREM_KINDS:
            status = ('kernel_closed' if closed else 'pending_direct_sorry'
                      if row['contains_sorry_directly'] else 'proof_written_dependencies_pending')
        else:
            status = 'definition' if closed else 'definition_pending_dependencies'
        declarations.append(row | {
            'source_kind': kind, 'file': file, 'line': span['start_line'],
            'original': name.removeprefix('ConditionalGoldbach.') in baseline, 'kernel_closed': closed,
            'status': status, 'pending_local_dependencies': [] if closed else pending_dependencies(name),
        })
    declarations.sort(key=lambda row: (row['file'], row['line'], row['name']))
    reviewed = {row['name'] for row in declarations if row['original']}
    expected = {'ConditionalGoldbach.' + name for name in baseline}
    if reviewed != expected:
        raise ValueError(f'Reviewed declaration coverage differs: {sorted(expected - reviewed)}')
    theorems = [row for row in declarations if row['source_kind'] in THEOREM_KINDS]
    original = [row for row in theorems if row['original']]
    public = {row['name']: row for row in declarations}
    report = {
        'scope': 'All project-owned Lean constants by origin module, including generated and private declarations.',
        'original_theorem_counts': counts(original), 'all_public_theorem_counts': counts(theorems),
        'original_definitions': len(baseline) - len(original), 'original_theorems': len(original),
        'compiled_constants': len(records), 'standard_axioms': sorted(STANDARD_AXIOMS),
        'unusual_axioms': unusual, 'admitted_constants': sorted(admissions),
        'declarations': declarations,
        'source_files': [{'file': str(path.relative_to(ROOT)),
                          'sha256': hashlib.sha256(path.read_bytes()).hexdigest()} for path in source_paths],
        'main_results': {name: public['ConditionalGoldbach.' + name]['status']
                         for name in ('theorem_1_1', 'theorem_1_2')},
    }
    (ROOT / 'proof-status.json').write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps({key: value for key, value in report.items()
                      if key not in ('declarations', 'source_files')}, ensure_ascii=False, indent=2))
    if unusual or admissions:
        raise SystemExit('Project-owned compiled constants include admissions or unapproved axioms.')


if __name__ == '__main__':
    main()
