#!/usr/bin/env python3
"""Read current Lean sources and report the explicit import closure."""
import collections
import datetime
import hashlib
import json
import re
import subprocess
from pathlib import Path

FORMAL = Path(__file__).resolve().parents[2]
ROOT = FORMAL.parent
GOLDBACH = (FORMAL / ".lake/packages/goldbach").resolve()
LEAN = Path(subprocess.check_output(["lake", "env", "lean", "--print-prefix"], cwd=FORMAL, text=True).strip()) / "src/lean"
OUT = Path(__file__).resolve().parent / "dependencies-imports.json"
manifest = json.loads((FORMAL / "lake-manifest.json").read_text())
roots = [("liLiuGoldbach", FORMAL), ("goldbach", GOLDBACH)]
for p in manifest["packages"]:
    if p["name"] != "goldbach":
        roots.append((p["name"], (FORMAL / ".lake/packages" / p["name"]).resolve()))
roots += [("Lean-toolchain", LEAN), ("Lake-toolchain", LEAN / "lake")]
CHAR_LITERAL = re.compile(r"'(?:[^'\\\n]|\\(?:[nrt0\\\"']|x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}))'")


def remove_comments(source):
    # Preserve line positions; support nested Lean block comments and strings.
    out, i, depth, in_string = [], 0, 0, False
    while i < len(source):
        c, pair = source[i], source[i:i+2]
        if depth:
            if pair == "/-":
                depth += 1
                out.extend("  ")
                i += 2
            elif pair == "-/":
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
        elif in_string:
            out.append(c)
            i += 1
            if c == "\\" and i < len(source):
                out.append(source[i])
                i += 1
            elif c == '"':
                in_string = False
        elif c == "'" and (char_match := CHAR_LITERAL.match(source, i)):
            out.extend(char_match[0])
            i += len(char_match[0])
        elif pair == "/-":
            depth = 1
            out.extend("  ")
            i += 2
        elif pair == "--":
            j = source.find("\n", i)
            j = len(source) if j == -1 else j
            out.extend(" " * (j - i))
            i = j
        else:
            out.append(c)
            in_string = c == '"'
            i += 1
    return "".join(out)


modules = {}
unresolved = set()
pending = ["LiLiuGoldbach"]
while pending:
    name = pending.pop()
    if name in modules or name in unresolved:
        continue
    matches = [(pkg, base / (name.replace(".", "/") + ".lean"))
               for pkg, base in roots]
    found = next(((pkg, path) for pkg, path in matches if path.is_file()), None)
    if found is None:
        unresolved.add(name)
        continue
    pkg, path = found
    data = path.read_bytes()
    raw = data.decode("utf-8")
    clean = remove_comments(raw)
    imports = []
    # Imports live in the header. Ignoring comments avoids commented examples.
    for lineno, line in enumerate(clean.splitlines(), 1):
        if not line.strip() or line.strip() in {"module", "prelude"}:
            continue
        m = re.match(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(.+)$", line)
        if m:
            for dep in m[1].split():
                imports.append({"module": dep, "line": lineno})
                pending.append(dep)
        else:
            break
    modules[name] = {
        "package": pkg,
        "path": str(path),
        "physical_lines": len(raw.splitlines()),
        "nonblank_noncomment_lines": sum(bool(line.strip()) for line in clean.splitlines()),
        "sha256": hashlib.sha256(data).hexdigest(),
        "imports": imports,
    }

by_package = collections.defaultdict(list)
for name, value in modules.items():
    by_package[value["package"]].append(name)

direct = []
for name in sorted(by_package["liLiuGoldbach"]):
    value = modules[name]
    for item in value["imports"]:
        if item["module"] in modules and modules[item["module"]]["package"] != "liLiuGoldbach":
            direct.append({"from_module": name, "from_file": value["path"],
                           "line": item["line"], "to_module": item["module"],
                           "to_package": modules[item["module"]]["package"]})


def git(*args):
    return subprocess.check_output(["git", "-C", str(GOLDBACH), *args], text=True).strip()


summaries = {}
for pkg, names in sorted(by_package.items()):
    summaries[pkg] = {
        "modules": len(names),
        "physical_lines": sum(modules[n]["physical_lines"] for n in names),
        "nonblank_noncomment_lines": sum(modules[n]["nonblank_noncomment_lines"] for n in names),
    }

report = {
    "generated_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "entry_module": "LiLiuGoldbach",
    "method": "Recursive traversal of current explicit Lean import headers, with nested block and line comments removed. Counts include the entry module. Implicit prelude imports are not added; reachable explicit imports are fully resolved. A module import does not establish that its theorems are used in a proof.",
    "line_count_definition": "physical_lines counts splitlines(); nonblank_noncomment_lines counts lines with text after removing nested Lean block comments and line comments, preserving string literals.",
    "scope": "Production entrypoint only; scratch files, scripts, reference files, and separate verification projects are excluded unless imported.",
    "lake_manifest": manifest,
    "source_roots": [{"package": p, "path": str(b)} for p, b in roots],
    "external_goldbach_repository": {
        "path": str(GOLDBACH), "head": git("rev-parse", "HEAD"),
        "origin": git("remote", "get-url", "origin"),
        "working_tree_status": git("status", "--porcelain"),
    },
    "summary_by_package": summaries,
    "direct_external_imports": direct,
    "goldbach_package_modules": sorted(by_package["goldbach"]),
    "goldbach_namespace_modules": sorted(n for n in modules if n == "Goldbach" or n.startswith("Goldbach.")),
    "LeanArchitect_modules": sorted(by_package["LeanArchitect"]),
    "ternary_project_source_roots": [str(p) for _, p in roots if "ternary" in str(p).lower()],
    "unresolved_imports": sorted(unresolved),
    "modules": dict(sorted(modules.items())),
}

report["goldbach_namespace_breakdown"] = dict(sorted(collections.Counter(
    n.split(".")[0] for n in report["goldbach_package_modules"]).items()))
report["goldbach_closure_by_direct_import"] = {}
for edge in direct:
    if edge["to_package"] != "goldbach":
        continue
    visited, stack = set(), [edge["to_module"]]
    while stack:
        n = stack.pop()
        if n in visited:
            continue
        visited.add(n)
        stack.extend(i["module"] for i in modules[n]["imports"] if i["module"] in modules)
    report["goldbach_closure_by_direct_import"][edge["to_module"]] = sorted(
        n for n in visited if modules[n]["package"] == "goldbach")

env_path = Path(__file__).resolve().parent / "declaration-audit/imported-modules.json"
if env_path.exists():
    actual = set(json.loads(env_path.read_text()))
    scanned = set(modules)
    report["compiled_environment_crosscheck"] = {
        "evidence_file": str(env_path),
        "source_module_count": len(scanned),
        "compiled_environment_module_count": len(actual),
        "source_only_modules": sorted(scanned - actual),
        "compiled_environment_only_modules": sorted(actual - scanned),
        "exact_match": actual == scanned,
    }
OUT.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
print(json.dumps({k: report[k] for k in ("summary_by_package", "direct_external_imports", "goldbach_package_modules", "goldbach_namespace_modules", "LeanArchitect_modules", "ternary_project_source_roots", "unresolved_imports")}, ensure_ascii=False, indent=2))
