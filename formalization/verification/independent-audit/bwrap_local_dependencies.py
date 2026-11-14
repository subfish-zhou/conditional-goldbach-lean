#!/usr/bin/python3
"""Preserve comparator sandboxing; expose the project and resolved package caches.

Lean's default sandbox hides /home, including absolute-path Lake dependencies.
Add read-only mounts after the home cover, before comparator's writable mounts.
All original namespace, environment, network and writable-path options survive.
"""
from pathlib import Path
import ctypes
import json
import os
import signal
import subprocess
import sys
import time

args=sys.argv[1:]
trace = os.environ.get('CONDITIONAL_GOLDBACH_COMPARATOR_TRACE')
if args[:1] == ['--trace-file']:
    trace, args = args[1], args[2:]
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
command = ['/usr/bin/bwrap'] + args[:insert] + extra + args[insert:]
if not trace:
    os.execv(command[0], command)

# Preserve the original --die-with-parent behavior through this timing parent.
# The sandbox's namespaces, environment clearing and mount permissions are
# unchanged; the trace is written by the host-side parent after the child exits.
parent = os.getppid()
libc = ctypes.CDLL(None, use_errno=True)
if libc.prctl(1, signal.SIGTERM, 0, 0, 0) != 0:  # PR_SET_PDEATHSIG
    raise OSError(ctypes.get_errno(), 'Cannot preserve comparator parent-death semantics')
if os.getppid() != parent:
    raise SystemExit(1)
start = time.monotonic()
result = subprocess.run(command)
inner = args[args.index('--') + 1:]
row = dict(command=inner, wall_seconds=time.monotonic() - start, exit_code=result.returncode)
with open(trace, 'a') as output:
    output.write(json.dumps(row) + '\n')
if result.returncode < 0:
    os.kill(os.getpid(), -result.returncode)
raise SystemExit(result.returncode)
