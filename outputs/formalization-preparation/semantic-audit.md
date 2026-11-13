# Semantic review: historical snapshot

The type checks and source hashes recorded here belong to the **pre-rename review snapshot**. Current theorem-type checks are in [reviewed-types.json](../../formalization/reviewed-types.json); [naming-migration.json](../../formalization/verification/naming-migration.json) records the original Git blobs and before/after hashes. [snapshot-migration.json](snapshot-migration.json) records the current snapshot's byte-for-byte match to the Reviewed reference and the unchanged TeX hash.

[Detailed Chinese ledger](semantic-audit.zh.md) · [Structured ledger](semantic-audit.json) · [Current independent audit](../../formalization/verification/independent-audit/report.html)

Revision 9 reviewed **38 named results and 121 definition families**. The statement snapshot contains **102 theorem statements and 171 definition declarations**, with placeholder proofs. The recorded type check succeeded. Historical hashes in the ledgers identify the corresponding review revisions.

## Corrections recorded during review

- Replaced `ContDiff ℝ ⊤` with `ContDiff ℝ ∞` for the smooth compactly supported weight class. In the pinned environment, `⊤` denotes the analytic order.
- Restored Appendix A.2's intended conditional GRH quantifiers and kept the order of constants and the admissible function `h`.
- Added joint meromorphic statements and the required convergence, integrability, trace, and spectral-product interfaces.
- Added Appendix A.1's variable-boundary kernel representation, boundary L², action integrability, and spectral-data existence obligations under the original hypotheses.
- Distinguished the real weight `V(u) = Φ(u) − uΦ′(u)` from the complex contour factor `Ψ_N(s)` in Proposition 7.4.
- Restored the Appendix B symbols `η`, `W`, and `f`, and the pole coefficient `C_{N,γ}` in Appendix A.4.
- Exposed the general odd-character orthogonality formula, the punctured Perron residue, and the Poisson action at parameter zero as supporting interfaces.
- Displayed all three component bounds in Proposition 6.5 separately.
- Extracted `theorem_6_1_abstract_dictionary` for the common fixed-strip and variable-strip spectral argument.

The dependency order is `5.3 → 5.4` and `6.4 → 6.5 → Theorem 6.2`. The declaration and paper dependency graphs record construction obligations separately.

## Mathematical encodings reviewed

| Encoding | Representation obligations |
|---|---|
| Joint meromorphy by common nonzero entire denominators | Equality on the denominator's nonzero domain and the required global identities |
| Hardy spaces as weighted Fourier–Laplace L² | Unique holomorphic realization, linearity, isometry, and boundary traces |
| Countable Hilbert bases for Hilbert–Schmidt and spectral data | Actual eigenvector equations, square summability, zero-padding invariance, and basis independence |
| Specialized positive trace-class and Fredholm interfaces | Existence, trace identities, spectral-choice independence, and the `T²` determinant bridge |
| Quaternionic slices from one complex entire function | Conjugation compatibility, all-slice identities, and multiplicity transfer |

These were recorded as representation choices at the statement-review stage. Their later mathematical and mechanical checks are documented in the independent audit.

## Evidence

[TeX review](tex-audit.md), [TeX ledger](tex-audit.json), [interface cross-check](tex-cross-check.json), [dependency ledger](dependency-audit.json), and [abstract dictionary check](abstract-bridge-cross-check.json) contain the detailed source clauses, quantifiers, and review findings. `verification.json` records the historical snapshot's type-check evidence.
