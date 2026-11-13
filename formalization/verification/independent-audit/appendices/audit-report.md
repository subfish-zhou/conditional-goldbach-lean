# Independent audit of Appendices A and B

[Detailed Chinese report](audit-report.zh.md) · [Proposition comparisons](comparison.json) · [Definition comparisons](definitions-comparison.json)

Original TeX lines **3931–4599** were checked against the current implementation. The audit covers **18 complete propositions**: 9 named results, 8 reviewed supporting statements, and `variable_uniform_spectral_bound`. It covers **32 definition families** through **48 independently reconstructed definition bodies**, including two auxiliary definitions for A.3.

The checked statement clusters preserve the source hypotheses, quantifier order, coefficients, and definitions. Specific numerical inputs are listed separately below.

## Appendix A

| Statement | Checked mathematical content |
|---|---|
| A.1 | Fix `c > 0`; assume even `N ≥ 4`, `N > exp(10c)`, and GRH. The variable-strip quadratic identity and pointwise estimates retain these conditions. The norm asymptotic has constants depending on `φ,c`, with `c` fixed before `N → ∞`. |
| A.1 operator supplement | The variable-boundary kernel representation, boundary L², action integrability, and square-summable spectrum are conclusions under the same assumptions. |
| A.2 | The R/norm and zero-free-width/norm equivalences preserve the open half-space, `0 < η < 1/2`, and admissible S width `≤ 1/4`. Constants for the arithmetic errors precede `h`. |
| A.2 pointwise supplement | `∀φ,c ∃C>0 ∀N ∀h` expresses a constant independent of `h`. |
| `variable_uniform_spectral_bound` | `∀c>0 ∃C≥1,c0>0 ∃N0 ∀` sufficiently large even `N`; no `φ` or `h` parameter occurs. It supplies width `c0 S(N)/(N log N)`. |
| A.3 | `Qα ≍φ N^(2α)` uniformly for `0 < α < 1/10`; the absolute operator bound is `C((log N)² + α⁻²)`. |
| A.3 absolute bound | `∃C>0 ∃N0 ∀N ∀α`, with no weight parameter. |
| A.3 balance | For fixed `φ,C`, constants are uniform in admissible `N,c` and give `QαMα ≍φ (log N)²e^(2c)(1+c⁻²)`. |
| A.3 widths | The ratio of the two actual admissible widths has order `h²(log N)⁴/S(N)² · e^(4c)(1+c⁻²)²`. Positive scales and the inverse-width domains are retained. |
| A.4 | With `N` and a chosen zero ordinate `γ` fixed, `liminf(c→0+) c‖TN,c‖ ≥ 2 C_N,γ log N/(1+γ²) > 0`. The coefficient averages squared analytic multiplicities. The small-`c` domain gives `‖T‖ ≥ z/c`, failure of R, and `η ≤ δ²c²/(3z²)`. |
| A.4 Euler supplement | The regular Euler product is analytic near zero and satisfies `S(N)RN(0)=1`, for even `N≥4`. |

The A.2 baseline width is the width supplied by the proved norm bound. A.4's lower-limit statement is expressed by `∀ε>0 ∃c0>0 ∀0<c<c0`, with `N,γ` fixed outside these quantifiers.

## Appendix B

Throughout the experiment, `N=30030`, `A=16`, and `L=1000`.

| Statement | Checked mathematical content |
|---|---|
| B.1 | The `C⁶` symmetric cutoff, the actual wide weight, and `rG=NJ/2−Cpp/2+E`. The prime-power correction sums ordered pairs with at least one exponent ≥2 and divides by the product of exponents; the final formula divides this correction by 2. |
| B.2 | Absolute convergence and `Iχ=−Σaₙχ(n)`, with all 5760 characters. `J=Σχχ(−1)|Iχ|²/5760` and `D=Σχ|Iχ|²/5760`. The logarithmic derivative is evaluated on the `3/2` line. |
| B.3 | For arbitrary approximations and a certified RMS error `ε≥0`, `|J−Ĵ|≤2√D̂ ε+ε²`, and the exact integer count lies in the resulting closed interval. |
| B.3 main identity | `A=NS cf/2` and `rG=A−NB/2−Cpp/2+E`, with `cf=∫₀¹ f(u)f(1−u)du`. |
| B.4 | Under GRH, `B=⟨TvW,vW⟩`; the functional is integrable, bounded, linear, and represented by the actual Riesz vector. |
| B.4 weight supplement | The wide weight has `C⁶` regularity and compact support in `(0,1)`. The model uses its cross mass `∫f(u)f(1−u)du`. |
| B.5 | The matrix has 2562 nodes: 1281 on each boundary, from `−40` to `40` in steps of `1/16`, with endpoint half-weights. The matrix is `√wi E(si,conj sj)/((1+si)(1+conj sj)) √wj`. Its real spectrum is tied to a unitary diagonalization and its norm is the induced complex Euclidean norm. Under the stated GRH context, `‖C‖≤δ` implies every zero has real part `1/2`. |

The finite matrix product is

`det(I−4q(1−q)C²/δ²) = ∏j(1−4λj²q(1−q)/δ²)`.

## Numerical claims and remaining certificates

The general identities and criteria above are proved. The following table uses the current numerical audit ledger.

| TeX lines | Reported computation | Certificate status |
|---|---|---|
| 4341–4345 | 75 edge prime pairs and 26 unordered proper-prime-power pairs; E = 44.35776816334822525… and Cpp/2 = 10.16758713116445818… | The exact symbolic identity is proved in B.1. These numerical values remain uncertified. |
| 4389–4403 | h = 0.1, T = 1600, 2^20 FFT grid, 24 Euler–Maclaurin terms, height reset 32; Jhat ≈ 0.05799599193959489 and Dhat ≈ 0.29331844084848136 | The 5760 approximate character integrals, numerical integration implementation, and rational certificates connecting these outputs to integralI remain to be formalized. |
| 4408–4419 | Hardy–Littlewood prediction ≈ 908.1405628685 and wide-weight A ≈ 851.831147718741; 65-digit integration and accelerated C2 parameters | wideMainIntegral has an exact definition. The displayed approximations and the numerical Hardy–Littlewood integral remain uncertified. |
| 4420–4421 | A − Cpp/2 + E ≈ 886.021328750925 | The symbolic correction identity is proved; this decimal value remains uncertified. |
| 4430–4437 | −N Bhat/2 ≈ 18.978671254276 and rhat ≈ 905.0000000052 | B.3 accepts arbitrary approximate character integrals. A specific input array and this numerical center remain to be certified. |
| 4475–4486 | 3280 nonzero coefficients a_n; rational finite-transform enclosures give RMS integral error < 1.68935 × 10^−5 | This concrete error bound is an outstanding input to B.3. HasMomentError defines the condition, and lemma_B_3 assumes it. |
| 4487–4490 | Count error ≈ 0.274758682716; outward-rounded interval [904.725241, 905.274759] contains only the integer 905 | The general integer-enclosure theorem is proved. Propagating the actual numerical integration error into this particular interval remains to be certified. |
| 4491–4496 | Exactly 905 unordered prime pairs and 1810 ordered pairs; direct rational summation and independent prime enumeration | The audit supplement certifies the unordered count 905 by Lean-kernel enumeration. The integral-error route to 905, rational correction values, and remaining numerical displays are still outstanding. |
| 4501–4505 | α at N = 30030 ≈ 0.09699366 | The exact parameter and placement of 1/9 inside the strip are proved. The decimal display remains uncertified. |
| 4571–4580 | Numerical L′/L and Euler products with prime cutoff 2 × 10^5; extreme eigenvalues ≈ −0.353421 and 0.357462; norm ratio ≈ 0.826864 < 1; δ ≈ 0.432310239587548 | B.5 proves the critical-line conclusion assuming the exact matrix norm is at most δ. A certified numerical matrix approximation and norm bound remain outstanding. |
| 4577–4599 | Doubling the cutoff from 10^5 changes the extreme eigenvalues by < 3 × 10^−8; displayed zeros and figures use the full computed spectrum | The figures and cutoff-stability calculations remain numerical evidence for the finite model. A bound for the infinite operator is outside this numerical certification. |

## Comparison targets

The current mappings contain **18 propositions**, **48 definition bodies**, and **32 definition families**.

| Proposition | Original TeX lines |
|---|---|
| `ConditionalGoldbach.proposition_A_1` | 3949–3989 |
| `ConditionalGoldbach.proposition_A_1_operator_spec` | 3954–4004 |
| `ConditionalGoldbach.proposition_A_2` | 4018–4100 |
| `ConditionalGoldbach.proposition_A_2_pointwise` | 4058–4068 |
| `ConditionalGoldbach.variable_uniform_spectral_bound` | 4053–4056 |
| `ConditionalGoldbach.lemma_A_3` | 4110–4134 |
| `ConditionalGoldbach.lemma_A_3_absolute_operator_bound` | 4112–4119 |
| `ConditionalGoldbach.lemma_A_3_balance` | 4119–4134 |
| `ConditionalGoldbach.lemma_A_3_width_ratio` | 4127–4159 |
| `ConditionalGoldbach.proposition_A_4` | 4181–4208 |
| `ConditionalGoldbach.proposition_A_4_baseline_product` | 4221–4229 |
| `ConditionalGoldbach.proposition_B_1` | 4286–4327 |
| `ConditionalGoldbach.lemma_B_2` | 4351–4378 |
| `ConditionalGoldbach.lemma_B_3` | 4443–4463 |
| `ConditionalGoldbach.lemma_B_3_main_integral` | 4413–4428 |
| `ConditionalGoldbach.proposition_B_4` | 4501–4520 |
| `ConditionalGoldbach.proposition_B_4_weight` | 4522–4530 |
| `ConditionalGoldbach.proposition_B_5` | 4533–4561 |

The complete definition targets and family mapping are in [definitions-comparison.json](definitions-comparison.json) and [definition-families.json](definition-families.json).

## Evidence

`Reference.lean` reconstructs the propositions and appendix-specific formulas. All **48 `rfl` definition bridges** and **18 complete proposition assignments** compiled successfully. `definition-families.json` maps all 32 families. The independent review checks the mathematical correspondence from TeX; the consolidated [comparator results](../final-comparison.json) check the Lean reference against the implementation.
