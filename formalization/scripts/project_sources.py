"""Read only source files reachable from the actual Lean library import graph."""
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parents[1]


def declaration_source(path, span):
    """Read the source slice corresponding to a Lean declaration range."""
    lines = path.read_text().splitlines()
    chunk = lines[span['start_line'] - 1:span['end_line']]
    chunk[-1] = chunk[-1][:span['end_column']]
    chunk[0] = chunk[0][span['start_column']:]
    return '\n'.join(chunk)


def source_declarations(path):
    """Read top-level names with their actual nested namespace prefixes.

    Lean's compiled environment remains the authority: audit_proofs checks that
    every extracted public name exists, then asks Lean for its transitive axioms.
    """
    stack = []
    declaration = re.compile(r'^(?:(?:noncomputable|private|protected|local)\s+)*(def|abbrev|structure|theorem|lemma)\s+([\w.]+)')
    for line_number, line in enumerate(path.read_text().splitlines(), 1):
        namespace = re.match(r'^namespace\s+([\w.]+)\s*$', line)
        section = re.match(r'^(?:@\[expose\]\s+)?(?:(?:noncomputable|public)\s+)?section(?:\s+([\w.]+))?\s*$', line)
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

def library_sources(root=ROOT):
    todo=[root/'ConditionalGoldbach.lean'];seen=set()
    while todo:
        p=todo.pop()
        if p in seen:continue
        if not p.exists():raise FileNotFoundError(p)
        seen.add(p)
        for line in p.read_text().splitlines():
            m=re.match(r'^(?:public\s+)?import\s+(.+)$',line)
            if not m:continue
            for module in m[1].split():
                if module=='ConditionalGoldbach' or module.startswith('ConditionalGoldbach.'):
                    todo.append(root/('/'.join(module.split('.'))+'.lean'))
    return sorted(p for p in seen if p.name!='ConditionalGoldbach.lean')


def declaration_owner(name, root=ROOT):
    """Locate a public declaration in the reachable production sources."""
    owners = [path for path in library_sources(root)
              if any(row['name'] == name and not row['private']
                     for row in source_declarations(path))]
    if len(owners) != 1:
        raise ValueError(f'Expected one source owner for {name}, found {owners}')
    return owners[0].relative_to(root).as_posix()
