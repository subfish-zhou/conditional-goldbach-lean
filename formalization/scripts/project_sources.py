"""Read only source files reachable from the actual Lean library import graph."""
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parents[1]

def source_declarations(path):
    """Read top-level names with their actual nested namespace prefixes.

    Lean's compiled environment remains the authority: audit_proofs checks that
    every extracted public name exists, then asks Lean for its transitive axioms.
    """
    stack = []
    declaration = re.compile(r'^(?:(?:noncomputable|private|protected|local)\s+)*(def|abbrev|structure|theorem|lemma)\s+([\w.]+)')
    for line_number, line in enumerate(path.read_text().splitlines(), 1):
        namespace = re.match(r'^namespace\s+([\w.]+)\s*$', line)
        section = re.match(r'^(?:noncomputable\s+)?section(?:\s+([\w.]+))?\s*$', line)
        end = re.match(r'^end(?:\s+([\w.]+))?\s*$', line)
        if namespace:
            stack.append(('namespace', namespace[1]))
        elif section:
            stack.append(('section', section[1] or ''))
        elif end:
            if end[1]:
                index = next((i for i in range(len(stack)-1, -1, -1) if stack[i][1] == end[1]), None)
                if index is None:
                    raise ValueError(f'Unmatched end in {path}:{line_number}')
                del stack[index:]
            elif stack:
                stack.pop()
        match = declaration.match(line)
        if match:
            prefix = '.'.join(name for kind, name in stack if kind == 'namespace')
            name = prefix + '.' + match[2] if prefix else match[2]
            yield {'name': name, 'source_kind': match[1], 'line': line_number,
                   'private': bool(re.match(r'^(?:noncomputable\s+)?private\s', line))}

def library_sources():
    todo=[ROOT/'LiLiuGoldbach.lean'];seen=set()
    while todo:
        p=todo.pop()
        if p in seen:continue
        if not p.exists():raise FileNotFoundError(p)
        seen.add(p)
        for line in p.read_text().splitlines():
            m=re.match(r'^(?:public\s+)?import\s+(.+)$',line)
            if not m:continue
            for module in m[1].split():
                if module=='LiLiuGoldbach' or module.startswith('LiLiuGoldbach.'):
                    todo.append(ROOT/('/'.join(module.split('.'))+'.lean'))
    return sorted(p for p in seen if p.name!='LiLiuGoldbach.lean')
