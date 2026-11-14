"""Content fingerprints for proof verification."""
import hashlib
import json
from pathlib import Path
import subprocess

from project_sources import library_sources

BUILD_INPUTS = ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json')
BUILD_COMMAND = ('lake', '--wfail', 'build')
REVIEW_INPUTS = ('reference/Reviewed.lean', 'reference/declarations.json')
CONTROLS = ('condition', 'quantifier', 'definition')
COMPARATOR_AXIOMS = frozenset(('propext', 'Classical.choice', 'Quot.sound'))
FULL_TYPE_CHECK = ('lake', 'lean', 'TexAuditComparator/CheckTypes.lean')
PUBLICATION = 'verification/publication/'
DECLARATIONS = PUBLICATION + 'declaration-audit/'
DEPENDENCY_OUTPUTS = {
    'dependency-graph': (DECLARATIONS + 'imported-modules.json',),
    'dependency-analysis': (DECLARATIONS + 'summary.json',),
    'dependency-imports': (PUBLICATION + 'dependencies-imports.json',),
}


def read_json(path):
    return json.loads(path.read_text())


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fingerprints(root, paths):
    return {str(path): sha256(root / path) for path in sorted(paths)}


def build_inputs(project):
    sources = [path.relative_to(project) for path in library_sources(project)]
    paths = {Path(name) for name in (*BUILD_INPUTS, *REVIEW_INPUTS, 'ConditionalGoldbach.lean')}
    return fingerprints(project, paths.union(sources))


def manifest_revisions(project):
    return {row['name']: row['rev'] for row in read_json(project / 'lake-manifest.json')['packages']}


def pinned_dependencies(project):
    """Check the actual Lake checkouts against the Git revisions in the manifest."""
    revisions = manifest_revisions(project)
    for name, revision in revisions.items():
        directory = project / '.lake/packages' / name
        head = subprocess.check_output(
            ['git', '-C', str(directory), 'rev-parse', 'HEAD'], text=True).strip()
        dirty = subprocess.check_output(
            ['git', '-C', str(directory), 'status', '--porcelain'], text=True)
        if head != revision or dirty:
            raise ValueError(f'Lake package {name} must be clean at {revision}')
    return revisions


def comparator_targets(manifest, config):
    targets = [row['comparator_target'] for row in manifest['statements'] + manifest['definitions']]
    targets += manifest['semantic_bridges'] + manifest['numerical_cross_checks']
    if (len(set(targets)) != len(targets) or len(targets) != manifest['target_count']
            or len(config['theorem_names']) != len(targets)
            or set(config['theorem_names']) != set(targets)):
        raise ValueError('Comparator target inventory differs from the independent manifest')
    if (config['challenge_module'] != 'TexAuditComparator.Challenge'
            or config['solution_module'] != 'TexAuditComparator.Solution'
            or set(config['permitted_axioms']) != COMPARATOR_AXIOMS):
        raise ValueError('Comparator modules or permitted axioms differ')
    return targets


def comparator_inputs(project, audit, manifest):
    staged = audit / 'comparator-project'
    paths = [
        audit / 'comparator-manifest.json',
        audit / 'frozen-source-hashes.json',
        audit / 'bwrap_local_dependencies.py',
        *(audit / name for name in manifest['frozen_references']),
        *(staged / name for name in (*BUILD_INPUTS, 'comparator.json', 'TexAuditComparator.lean')),
        *(staged / f'control-{name}.json' for name in CONTROLS),
        *sorted((staged / 'TexAuditComparator').glob('*.lean')),
    ]
    return build_inputs(project) | fingerprints(project, [path.relative_to(project) for path in paths])
