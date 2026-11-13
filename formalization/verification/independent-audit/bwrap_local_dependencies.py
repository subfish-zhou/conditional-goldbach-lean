#!/usr/bin/python3
"""Preserve comparator sandboxing; expose the project and resolved package caches.

Lean's default sandbox hides /home, including absolute-path Lake dependencies.
Add read-only mounts after the home cover, before comparator's writable mounts.
All original namespace, environment, network and writable-path options survive.
"""
from pathlib import Path
import os, sys

args=sys.argv[1:]
assert '--unshare-all' in args and '--clearenv' in args and '--die-with-parent' in args
assert '--tmpfs' in args and '/home' in args
project=Path(__file__).resolve().parents[2]
packages=project/'.lake/packages'
dependencies={project}
if packages.exists():
    # A package directory or the whole packages tree may reuse an external cache.
    for candidate in [packages, *packages.iterdir()]:
        if candidate.is_dir():
            resolved=candidate.resolve()
            if not resolved.is_relative_to(project):
                dependencies.add(resolved)
# A mounted dependency already exposes any package caches below it.
mounts=[]
for directory in sorted(dependencies, key=lambda p: (len(p.parts), str(p))):
    if not any(directory.is_relative_to(parent) for parent in mounts):
        mounts.append(directory)
insert=args.index('--bind') if '--bind' in args else args.index('--setenv')
extra=[part for directory in mounts for part in ['--ro-bind',str(directory),str(directory)]]
os.execv('/usr/bin/bwrap',['bwrap']+args[:insert]+extra+args[insert:])
