# Independent audit of Sections 5–7

[Detailed Chinese report](report.zh.md) · [Statement and definition index](semantic-matrix.md)

The review read original TeX lines **1823–3858** and checked the current Lean definitions and complete theorem types. It covered **54 propositions**: 17 named results, 35 reviewed supporting statements, and 2 Hardy construction obligations. It also checked **32 definition families**, including the related Section 2 definitions.

All reviewed statement clusters matched their source clauses with the representation bridges described below. `statement-matrix.json` and `definition-matrix.json` record source lines, hypotheses, quantifiers, current declarations, and review findings.

## Representation and formula checks

1. **Hardy spaces.** `HardySpace a b` uses weighted frequency-space L². The independent `RawHardy` states holomorphy and bounded paired vertical-line L² integrals. Lemma 5.2 proves unique Fourier–Laplace representation, the exact supremum norm, and the two L² boundary limits. Supporting results establish linearity, closed trace image, trace norm, and boundary inner product.
2. **Integral operators.** Proposition 5.3 proves `RepresentsKernel` under the paper's assumptions; its integrability supplement covers both boundary integrals for every Hardy vector and interior point. `RepresentsKernel.unique` and the independent `selected_operator_unique` bridge establish uniqueness. The three components have their own representation and integrability results and satisfy `T = P − D − K`.
3. **Normalization.** The boundary inner product is the sum of two positive arc-length integrals. `paperInner u v = inner ℂ v u` is linear in its first argument. Fourier–Laplace uses `(2π)^(-1/2)`; the upward vertical Mellin parametrization uses `(2π)^(-1)`. The reproducing kernel has coefficient `1/(4Δ)` and the norm bound `1/(8d)`.
4. **Component estimates.** Proposition 6.5 includes positive trace class for P and D, Hilbert–Schmidt K, and all three bounds: `HS(P) ≤ tr(P) ≤ C(log²N + α⁻²)`, `HS(D) ≤ tr(D) ≤ Cα⁻²`, and `HS(K) ≤ Cα⁻²`. The constant precedes `N`. `ComponentNormBounds.component_bounds_of_average` also places the same constant before arbitrary `0 < a < β`.
5. **Spectral data.** `SpectralData T` includes a Hilbert basis, actual eigenvector equations, and square summability. Zero-padding bridges show that adding zero eigenvalues leaves the product and square sum unchanged. Spectral-choice and permutation invariance connect the constructions to the actual operator.
6. **Quaternionic products and determinants.** Factors are `1 − 4μ²q(1−q)/δ²`. Standard and arbitrary-slice bridges use a single conjugation-compatible complex entire function. The determinant is that of `T.comp T`, with `tr(T²) = Σμ² = HS²`. The checked statement cluster includes normalization at 0 and 1, symmetries, real critical values, all three zero cases, central order, and multiplicity preservation.
7. **Spectral dictionary.** The open zero-free half-space `Re q > 1−η` corresponds to the closed norm bound `‖T‖ ≤ δ/(2√(η(1−η)))`, for `0 < η < 1/2`. The hypotheses `M > δ`, `‖T‖ ≤ M`, and the formula for `η(M)` are retained. The baseline constants and eventual threshold are uniform.
8. **Mellin and quadratic identities.** The character integral has a minus sign, the double moment has a plus sign, and the Beta model integral is `−cφS`. The residual is `r = P−D+cφS = cφS−G`. Absolute convergence is supplied by explicit integrability statements. Proposition 7.4 covers every inner contour, continuity, the exact Riesz norm, the uniform bound, and `Oφ(1/log N)`. Theorem 7.1 gives the signed equality `cφS−G = ⟨Tv,v⟩`, with uniform error constant `e² weightEnergy φ`.

## Encoding details

- `PositiveKernel` supplies nonnegativity of the real quadratic form. The character kernel's proved Hermitian property supplies reality; the independent bridges check their combination.
- Hilbert–Schmidt and positive trace-class definitions use natural-number-indexed Hilbert bases in the paper's separable infinite-dimensional setting. Basis-independence, spectral-sum, and trace bridges are present.
- `sumConvolution` integrates over the positive half-line. Under `IsWeight`, `lemma_7_2_convolutions` proves equality with the paper's finite-interval formula.
- The inventory name `rankOneOperator` maps to Mathlib's `InnerProductSpace.rankOne`, whose required action formula is checked in `proposition_6_5_diagonal_vector_spec`.
- `NeZero N` and `alpha N < beta` support Lean's type constructions and follow from the standing size assumptions; `arithmetic_strip_nonempty` checks the latter.

## Mechanical record

`Reference.lean` contains **54 complete expected propositions** and **26 formula-level definitions**. All 54 proof assignments and all 26 `rfl` definition bridges compiled successfully. The four generic propositions retain their universe parameter. `Bridges.lean` supplies the independent representation checks above and compiled successfully.

This report records the section review and local compilation. The consolidated [comparator results](../final-comparison.json) contain the later comparison run. The TeX-to-reference step is mathematical review; the reference-to-implementation step checks Lean types and definition bodies.
