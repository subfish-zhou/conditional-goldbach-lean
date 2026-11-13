# Formalization inventory: review snapshot

The type checks and source hashes recorded here belong to the **pre-rename review snapshot**. Current theorem-type checks are in [reviewed-types.json](../../formalization/reviewed-types.json); [naming-migration.json](../../formalization/verification/naming-migration.json) records the original Git blobs and before/after hashes. [snapshot-migration.json](snapshot-migration.json) records the current snapshot's byte-for-byte match to the Reviewed reference and the unchanged TeX hash.

[Detailed Chinese tables](report.zh.md) · [Current proof library](../../formalization/README.md)

Revision 9 covers **38 independently named results and 121 definition families** from the paper and Appendices A and B. Repeated previews in Section 2 are counted once. The snapshot has **102 theorem statements**: 38 principal statements, 60 supporting statements, and 4 auxiliary statements. It also has 171 definition declarations.

[Reviewed Lean source](conditional-goldbach.lean) · [Original TeX](conditional-goldbach.tex) · [Structured inventory](inventory.json) · [Semantic review](semantic-audit.md) · [Dependency review](dependency-audit.md)

This is the statement-review stage, with placeholder proofs. The recorded Lean 4.35.0 type check succeeded using Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`. The current completed proofs and their verification status are documented in the proof library.

## Mathematical conventions

1. The paper's inner product is linear in the first argument: `paperInner u v = inner ℂ v u` converts Mathlib's convention.
2. The paper's singular series is `2 * liuSingularSeries N`.
3. Hardy spaces use weighted `Lp ℂ 2`, with separate theorems for holomorphic realization, unique Fourier–Laplace representation, boundary traces, and the exact norm.
4. Selected kernel operators, Riesz vectors, spectra, and traces have explicit representation and existence obligations. Their total definitions are used together with those obligations.
5. Hilbert–Schmidt and positive trace-class interfaces use natural-number-indexed Hilbert bases for the paper's separable infinite-dimensional Hardy spaces. Appendix B handles finite matrices separately.
6. Analytic constructions at fixed `N` and bounds uniform in `N` are stated separately. Constants, the admissible function `h`, and Appendix A's fixed parameter `c` retain their specified quantifier order.
7. Quaternionic spectral products are limits of ordered finite products. Supporting declarations connect them to complex products and establish invariance under reordering and spectral choices.
8. `diagonalVector` is a function; `diagonalHardyVector` supplies its Hardy-space realization. Rank-one operators use Mathlib's `InnerProductSpace.rankOne`.
9. Appendix A.3 compares the two actual `spectralWidthFromBound` quantities within their domains of validity.

## Results by part

| Part | Mathematical content |
|---|---|
| Theorems 1.1–1.2 | Weighted Goldbach asymptotics under GRH and spectral S/R; weight existence and `R ⇒ S` |
| Section 3 | Odd-character projection, character kernels, completed L-function zero expansions, Mellin moments |
| Section 4 | Beta integrals, meromorphic identities, singular density, model continuation, analytic residual |
| Section 5 | Hardy realization, boundary traces, kernel operators, Hilbert–Schmidt and reproducing-kernel identities |
| Section 6 | Spectral products, symmetries, zero classification, spectral dictionary, uniform component bounds |
| Section 7 | Mellin inversion, convolutions, residual integral, Riesz functional, exact quadratic identity, asymptotic estimates |
| Appendix A | Variable strips, uniform spectral estimates, boundary balance, small-boundary pole obstruction |
| Appendix B | Wide weights, exact count formulas, moment-error propagation, wide-weight quadratic identity, finite spectral model |

The [inventory](inventory.json) gives the full named-result and definition-family mappings, original formulas, and declaration locations. The Chinese companion retains the original detailed tables.

## Numerical work

Appendix B's exact symbolic identities and error-propagation theorem have been implemented in the proof library. The specific integral-error certificate, the integer interval derived from those inputs, and the finite matrix's numerical norm certificate remain open. A later [direct enumeration certificate](../../formalization/verification/independent-audit/appendices/NumericCrossCheck.lean) establishes the count 905 independently.
