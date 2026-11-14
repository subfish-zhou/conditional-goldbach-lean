# Development and public interfaces

[中文](development.zh.md)

Run commands below from `formalization/`. Lean, Mathlib and the number-theory
dependency remain pinned by the toolchain and Lake manifest.

## Daily checks

```bash
python3 scripts/check_project.py
```

Lake incrementally rebuilds changed modules and their dependents with warnings
treated as errors. The runner then checks source reachability, local elaboration
options, all import consumers, 171 reviewed definition bodies, 102 reviewed theorem
types, the frozen public API, and transitive axioms of every project-owned compiled
constant. Results and logs go to a fresh `.lake/development-check-*` directory.
The runner leaves release evidence untouched and labels its result `development`.

`python3 scripts/check_project.py --reuse-release` first tries the existing complete
release evidence. Reuse requires matching source, policy, tool, dependency and
output hashes. If it is stale, the command runs the development checks instead.
It never promotes a development result to a completed independent comparison.

## Release verification

On Linux, install `bubblewrap` and the optional page tools first:

```bash
python3 -m pip install -r requirements-review.txt
npm ci
npx playwright install chromium
python3 scripts/verify_project.py
python3 scripts/render_verified.py
python3 scripts/test_verification.py
python3 scripts/package_verified.py
```

Release verification retains all 218 independent Comparator targets, 103 full-type
checks and the three deliberately invalid controls. It also rebuilds the complete
library, checks the public API, and refreshes the dependency reports. The sandbox
adapter measures each dependency-resolution, build, export and kernel subprocess
without changing the sandbox's mounts, environment clearing or namespace policy.
The parent process preserves `--die-with-parent` semantics. Phase logs are hashed
into the verification evidence; parent-side comparison time remains part of the
overall Comparator wall time.

`render_verified.py` renders and browser-checks both report languages before binding
the release record. Tests cover exact source reconstruction, all declaration scopes,
LaTeX, initial deep links, mobile width and operation without network requests.

The GitHub workflow runs development checks on pull requests and the complete
release sequence on `main` pushes and manual dispatch. Actions are pinned by commit
hash. A run uploads its evidence or failure logs; publishing generated artifacts
back to the branch remains an explicit Git operation.

## Compatibility contract

`reference/public-api.json` freezes the 1,621 public source declarations of commit
`cb16bfc`. The checker compares structural fingerprints of elaborated types after
alpha-renaming universe parameters, removing expression metadata and erasing compiler-generated
binder hygiene scopes (which include the source module path). Explicit binder names,
order, implicitness, domains and conclusions remain significant. This check is
deliberately stricter than definitional equality and complements the paper-facing
Comparator. Newly added declarations are permitted; changing a frozen interface
requires an explicit compatibility decision rather than regenerating the baseline.

Old module paths and declaration names remain available through compatibility
imports or wrappers. Proof-only tactic imports are private: downstream proofs
should import the tactics they use. Production files cannot set file-wide heartbeat,
recursion-depth or transparency overrides; necessary exceptions belong to individual
declarations and should document their measured purpose.

## Reusable analysis

`ConditionalGoldbach.Analysis.L2Fourier` has only Mathlib in its external import and proof closure. The enclosing Lake package still pins `goldbach-lean`; this refactor does not change package downloads. It provides:

- agreement of classical and L² Fourier transforms for integrable L² functions;
- real dilation on L², its representative, continuity and exact norm scaling;
- the physical Fourier normalization and its norm-preservation theorem.

Hardy interior restrictions and boundary limits consume this interface. The old
`Proofs.HardyFourier` import preserves existing names. For example:

```lean
import ConditionalGoldbach.Analysis.L2Fourier

open MeasureTheory in
example (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖ConditionalGoldbach.Analysis.physicalFourierL2 f‖ = ‖f‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    (ConditionalGoldbach.Analysis.physicalFourierL2_norm_sq f)
```

`ConditionalGoldbach.Analysis.SpectralData` exposes coordinate identities and norm
bounds for the existing diagonal Hilbert-space data. Both spectral algebra and trace
proofs use it. Its imports exclude the Hardy constructions and arithmetic proofs.
The old `Proofs.SpectralDataAlgebra` entrypoint remains available.

`Definitions.GeometryCore` contains strip geometry and scale parameters with no
integration import. `Definitions.BoundaryIntegral` adds boundary integration, and
the original `Definitions.Geometry` reexports both. The consumer policy tests these
boundaries and compiles representative uses of the shared analysis interfaces.

These interfaces can be imported by other projects directly. Moving them into an
upstream repository is a separate integration step once its consumers and conventions
are established; the current dependency pins remain unchanged.
