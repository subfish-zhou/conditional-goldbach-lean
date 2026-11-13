"""Analyze the kernel-constant graph exported by DeclarationAudit.lean."""
import collections
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
EXTERNAL = (HERE.parents[2] / '.lake/packages/goldbach').resolve()
graph = json.loads((HERE / 'declaration-graph.json').read_text())
nodes = {r['name']: r for r in graph['declarations']}
project_modules = {
    r['module'] for r in nodes.values()
    if (EXTERNAL / (r['module'].replace('.', '/') + '.lean')).is_file()
}


def refs(n):
    r = nodes[n]
    return r['type_refs'] + r['value_refs'] + r['constructor_refs']


def closure(roots):
    parents = {n: None for n in roots}
    todo = collections.deque(roots)
    while todo:
        n = todo.popleft()
        for target in refs(n):
            if target not in parents:
                assert target in nodes, target
                parents[target] = n
                todo.append(target)
    return parents


def path_to(n, parents):
    path = [n]
    while parents[n] is not None:
        n = parents[n]
        path.append(n)
    return path[::-1]


scope_roots = {
    **{n: ['ConditionalGoldbach.' + n] for n in
       ['theorem_1_1', 'theorem_1_2', 'primePair_consequence']},
    'reviewed_102': json.loads((HERE / 'reviewed-names.json').read_text()),
    'public_library': [n for n in graph['local_roots'] if not nodes[n]['private']],
    'all_local_declarations': graph['local_roots'],
}
summary = {}
for scope, roots in scope_roots.items():
    parents = closure(roots)
    external = sorted(n for n in parents if nodes[n]['module'] in project_modules)
    by_module = collections.defaultdict(list)
    for n in external:
        by_module[nodes[n]['module']].append(n)
    boundaries = []
    for source in sorted(parents):
        if not nodes[source]['module'].startswith('ConditionalGoldbach'):
            continue
        for edge_kind in ['type_refs', 'value_refs', 'constructor_refs']:
            for target in nodes[source][edge_kind]:
                if nodes[target]['module'] in project_modules:
                    boundaries.append({
                        'source': source,
                        'source_module': nodes[source]['module'],
                        'edge_kind': edge_kind,
                        'target': target,
                        'target_module': nodes[target]['module'],
                    })
    result = {
        'root_count': len(roots),
        'reachable_declaration_count': len(parents),
        'external_project_declaration_count': len(external),
        'external_project_module_count': len(by_module),
        'external_project_modules': dict(sorted(by_module.items())),
        'external_direct_boundary_declaration_count': len({e['target'] for e in boundaries}),
        'external_direct_boundary_edges': boundaries,
        'axioms': sorted(n for n in parents if nodes[n]['kind'] == 'axiom'),
        'proof_witness_paths': {n: path_to(n, parents) for n in external},
    }
    (HERE / f'{scope}.json').write_text(json.dumps(result, indent=2, ensure_ascii=False) + '\n')
    summary[scope] = {k: v for k, v in result.items() if k not in
                      ['proof_witness_paths', 'external_project_modules', 'external_direct_boundary_edges']}
    summary[scope]['external_project_module_counts'] = {m: len(ns) for m, ns in sorted(by_module.items())}
    with (HERE / f'{scope}-external-declarations.tsv').open('w') as f:
        f.write('module\tname\tkind\tprivate\n')
        for n in external:
            r = nodes[n]
            f.write(f"{r['module']}\t{n}\t{r['kind']}\t{r['private']}\n")

(HERE / 'summary.json').write_text(json.dumps(summary, indent=2, ensure_ascii=False) + '\n')
print(json.dumps(summary, indent=2, ensure_ascii=False))
