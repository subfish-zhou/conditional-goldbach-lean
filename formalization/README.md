# Conditional Goldbach: proof library

[Chinese](README.zh.md) · [Proof explorer](progress.html) · [Axiom ledger](proof-status.json)

Lean 4 proofs of the reviewed Li–Liu statements, including the analytic, Hardy-space, operator, and spectral constructions. The main theorems give asymptotics for sufficiently large even integers under GRH and spectral condition S or R, with the original quantifier order and constant dependencies.

## Current status

**102 of 102 reviewed declarations** have complete transitive proof dependencies. The ledger records 0 declarations with written proofs and pending dependencies, and 0 direct placeholders. Across all public theorems and auxiliary results, **1354** have complete proof dependencies.

The 102 reviewed declarations cover the paper's 38 named results and their supporting clauses. The review also tracks 171 original definitions.

- `theorem_1_1`: `kernel_closed`.
- `theorem_1_2`: `kernel_closed`.
- `primePair_consequence`: `kernel_closed`.

Remaining numerical work in Appendix B: certify the specified integral approximations and their errors, derive the concrete integer interval from those inputs, and certify the finite spectral matrix numerically. The general error-propagation and spectral-criterion theorems are proved. A separate [direct enumeration certificate](verification/independent-audit/appendices/NumericCrossCheck.lean) establishes 905 unordered prime pairs for 30030.

## Build and verify

Run from this directory:

```bash
lake update
lake exe cache get
lake build
python3 scripts/audit_proofs.py
python3 scripts/check_reviewed_types.py
python3 scripts/check_definitions.py
python3 scripts/write_progress_report.py
python3 scripts/build_progress.py
```

The toolchain is Lean 4.35.0. Mathlib is pinned to `56a005855ea17e0b0958f73ec801ae140b0a1679`; the `goldbach-lean` Git dependency is pinned in `lakefile.toml` and `lake-manifest.json`. See [dependency details](../docs/dependencies.md).

HTML generation uses the optional packages in `requirements-review.txt` and `package.json`. The generated reports work offline.

## Library map

| Modules | Content |
|---|---|
| `BaseDefinitions.lean`, `Definitions.lean` | Reviewed objects, interior-line L², and boundary-trace existence |
| `Proofs/Weights.lean`, `WeightNorm.lean` | Smooth weights, positive mass, support, convolutions, and norm integrals |
| `Proofs/Characters.lean`, `Character*.lean`, `LFunction*.lean` | Odd-character projection, L-functions, zero expansions, and analytic kernels |
| `Proofs/Beta*.lean`, `Density*.lean` | Beta integrals, meromorphic identities, and singular-density Euler products |
| `Proofs/Hardy*.lean`, `Kernel*.lean` | Fourier–Laplace realization, traces, integral operators, and reproducing kernels |
| `Proofs/Spectral*.lean`, `DictionaryApplication.lean` | Spectral products, trace and determinant identities, zeros, and the spectral dictionary |
| `Proofs/Mellin*.lean`, `Quadratic*.lean` | Inversion, moment identities, Riesz representation, and the exact quadratic identity |
| `Proofs/QuantitativeBounds.lean`, `TotientLogLog.lean` | Uniform operator bounds and singular-series estimates |
| `Proofs/Variable*.lean`, `BalanceBounds.lean`, `PoleObstruction.lean` | Variable strips, boundary balance, and the small-boundary obstruction |
| `Proofs/Wide*.lean`, `FiniteExperimentSpectrum.lean` | Appendix B wide weights, count identities, and finite spectral criteria |
| `Proofs/PrimePowers.lean`, `PrimePairs.lean`, `Main.lean` | Prime-power removal, prime-pair consequence, and main theorem assembly |

## Verification evidence

- `proof-status.json`: Lean `collectAxioms` follows theorem types and proof values recursively. The permitted foundational axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- `reviewed-types.json`: definitional-equality checks compare all 102 complete theorem types against the statement snapshot, after mapping its namespace.
- `reviewed-definitions.json`: checks the declarations and bodies of the 171 reviewed definitions, ignoring whitespace and comments between declarations.
- `verification.json`: consolidated build and verification records.
- [Independent source audit](verification/independent-audit/report.html): original-TeX review, representation bridges, and comparator results.

`reference/Reviewed.lean` preserves the earlier statement-review snapshot. The main library imports the completed proof modules. Audit challenges use placeholders to specify expected targets; their solutions provide the corresponding proofs.

## Completed reviewed declarations

- [interiorLine_memLp](ConditionalGoldbach/Definitions.lean#L12)
- [boundaryTraces_exist](ConditionalGoldbach/Definitions.lean#L28)
- [proposition_6_5_components_spec](ConditionalGoldbach/Proofs/ArithmeticComponentOperators.lean#L108)
- [lemma_A_3_balance](ConditionalGoldbach/Proofs/BalanceBounds.lean#L36)
- [lemma_A_3_width_ratio](ConditionalGoldbach/Proofs/BalanceBounds.lean#L95)
- [proposition_A_4_baseline_product](ConditionalGoldbach/Proofs/BaselineEuler.lean#L123)
- [lemma_4_2](ConditionalGoldbach/Proofs/BetaIdentity.lean#L219)
- [lemma_4_1](ConditionalGoldbach/Proofs/BetaIntegrals.lean#L172)
- [lemma_4_1_absolute_convergence](ConditionalGoldbach/Proofs/BetaIntegrals.lean#L183)
- [lemma_4_1_signed_model](ConditionalGoldbach/Proofs/BetaIntegrals.lean#L195)
- [lemma_4_2_meromorphic](ConditionalGoldbach/Proofs/BetaMeromorphic.lean#L129)
- [proposition_3_2](ConditionalGoldbach/Proofs/CharacterAnalytic.lean#L108)
- [lemma_6_4](ConditionalGoldbach/Proofs/CharacterAverage.lean#L82)
- [proposition_3_2_joint_meromorphic](ConditionalGoldbach/Proofs/CharacterJoint.lean#L55)
- [lemma_3_4_paired_zero_sum](ConditionalGoldbach/Proofs/CharacterSeries.lean#L63)
- [lemma_3_4](ConditionalGoldbach/Proofs/CharacterZeroExpansion.lean#L53)
- [lemma_3_4_normal_convergence](ConditionalGoldbach/Proofs/CharacterZeroShiftNormal.lean#L26)
- [lemma_6_4_zero_poisson_convergence](ConditionalGoldbach/Proofs/CharacterZeroSummability.lean#L122)
- [lemma_3_1_odd_orthogonality](ConditionalGoldbach/Proofs/Characters.lean#L58)
- [lemma_3_1](ConditionalGoldbach/Proofs/Characters.lean#L360)
- [lemma_4_3_density_convergence](ConditionalGoldbach/Proofs/DensityConvergence.lean#L75)
- [lemma_4_3_euler_product_convergence](ConditionalGoldbach/Proofs/DensityEuler.lean#L146)
- [lemma_4_3](ConditionalGoldbach/Proofs/DensityEulerIdentity.lean#L98)
- [theorem_6_1](ConditionalGoldbach/Proofs/DictionaryApplication.lean#L34)
- [singularSeries_eq_existing](ConditionalGoldbach/Proofs/Elementary.lean#L10)
- [proposition_B_5](ConditionalGoldbach/Proofs/FiniteExperimentSpectrum.lean#L141)
- [lemma_3_3](ConditionalGoldbach/Proofs/HadamardLimit.lean#L110)
- [proposition_5_3](ConditionalGoldbach/Proofs/HardyArithmeticTheorems.lean#L33)
- [proposition_5_4_kernel_pairing](ConditionalGoldbach/Proofs/HardyArithmeticTheorems.lean#L47)
- [proposition_5_3_kernel_integrability](ConditionalGoldbach/Proofs/HardyArithmeticTheorems.lean#L55)
- [proposition_5_4](ConditionalGoldbach/Proofs/HardyArithmeticTheorems.lean#L66)
- [proposition_5_4_fixed_contour](ConditionalGoldbach/Proofs/HardyArithmeticTheorems.lean#L79)
- [lemma_5_2](ConditionalGoldbach/Proofs/HardyConverse.lean#L43)
- [proposition_5_4_exact_norm](ConditionalGoldbach/Proofs/HardyReproducing.lean#L138)
- [lemma_5_2_representation_spec](ConditionalGoldbach/Proofs/HardyTraceAlgebra.lean#L123)
- [lemma_5_2_closed_trace_space](ConditionalGoldbach/Proofs/HardyTraceAlgebra.lean#L181)
- [lemma_5_2_boundary_inner](ConditionalGoldbach/Proofs/HardyTraceAlgebra.lean#L198)
- [proposition_3_2_finite_rank](ConditionalGoldbach/Proofs/KernelAlgebra.lean#L106)
- [proposition_5_1](ConditionalGoldbach/Proofs/KernelRegularity.lean#L95)
- [proposition_5_1_fueter_equation](ConditionalGoldbach/Proofs/KernelRegularity.lean#L144)
- [theorem_7_1_uniform](ConditionalGoldbach/Proofs/Main.lean#L16)
- [theorem_1_1](ConditionalGoldbach/Proofs/Main.lean#L56)
- [theorem_1_2](ConditionalGoldbach/Proofs/Main.lean#L98)
- [lemma_7_1](ConditionalGoldbach/Proofs/MellinCharacterShift.lean#L107)
- [lemma_7_1_absolute_convergence](ConditionalGoldbach/Proofs/MellinCharacterShift.lean#L153)
- [lemma_7_2](ConditionalGoldbach/Proofs/MellinModelDouble.lean#L66)
- [lemma_7_2_absolute_convergence](ConditionalGoldbach/Proofs/MellinModelDouble.lean#L77)
- [lemma_3_5](ConditionalGoldbach/Proofs/MellinMoment.lean#L97)
- [lemma_3_5_absolute_convergence](ConditionalGoldbach/Proofs/MellinMomentComplete.lean#L10)
- [lemma_3_5_small_sigma](ConditionalGoldbach/Proofs/MellinMomentComplete.lean#L21)
- [proposition_7_3](ConditionalGoldbach/Proofs/MellinResidual.lean#L89)
- [proposition_7_3_absolute_convergence](ConditionalGoldbach/Proofs/MellinResidual.lean#L98)
- [proposition_4_4](ConditionalGoldbach/Proofs/ModelContinuation.lean#L88)
- [proposition_A_4](ConditionalGoldbach/Proofs/PoleObstruction.lean#L11)
- [primePair_consequence](ConditionalGoldbach/Proofs/PrimePairs.lean#L13)
- [lemma_7_5](ConditionalGoldbach/Proofs/QuadraticEstimates.lean#L37)
- [lemma_7_5_asymptotic](ConditionalGoldbach/Proofs/QuadraticEstimates.lean#L74)
- [proposition_7_4](ConditionalGoldbach/Proofs/QuadraticFunctional.lean#L11)
- [theorem_7_1](ConditionalGoldbach/Proofs/QuadraticIdentity.lean#L120)
- [proposition_6_5](ConditionalGoldbach/Proofs/QuantitativeBounds.lean#L23)
- [lemma_A_3_absolute_operator_bound](ConditionalGoldbach/Proofs/QuantitativeBounds.lean#L42)
- [lemma_A_3](ConditionalGoldbach/Proofs/QuantitativeBounds.lean#L53)
- [theorem_6_2](ConditionalGoldbach/Proofs/QuantitativeBounds.lean#L108)
- [proposition_4_5](ConditionalGoldbach/Proofs/ResidualAnalytic.lean#L85)
- [lemma_4_1_local_density](ConditionalGoldbach/Proofs/SingularDensity.lean#L63)
- [theorem_1_2_hypothesisR_implies_S](ConditionalGoldbach/Proofs/SpectralAlgebra.lean#L12)
- [theorem_6_1_width_comparison](ConditionalGoldbach/Proofs/SpectralAlgebra.lean#L24)
- [proposition_6_3_factor_central_order](ConditionalGoldbach/Proofs/SpectralAlgebra.lean#L126)
- [proposition_6_2](ConditionalGoldbach/Proofs/SpectralCompletion.lean#L81)
- [proposition_6_1_spectral_choice_independent](ConditionalGoldbach/Proofs/SpectralCompletionChoice.lean#L104)
- [proposition_6_1_square_determinant](ConditionalGoldbach/Proofs/SpectralCompletionDeterminant.lean#L37)
- [proposition_6_1](ConditionalGoldbach/Proofs/SpectralCompletionDeterminant.lean#L46)
- [proposition_6_1_enumeration](ConditionalGoldbach/Proofs/SpectralCompletionIdentities.lean#L53)
- [proposition_6_2_centered_product](ConditionalGoldbach/Proofs/SpectralCompletionIdentities.lean#L98)
- [proposition_6_2_critical_values](ConditionalGoldbach/Proofs/SpectralCompletionIdentities.lean#L154)
- [proposition_6_3_multiplicities](ConditionalGoldbach/Proofs/SpectralCompletionMultiplicities.lean#L86)
- [proposition_6_3_three_cases](ConditionalGoldbach/Proofs/SpectralCompletionZeros.lean#L91)
- [proposition_6_3](ConditionalGoldbach/Proofs/SpectralConsequences.lean#L33)
- [proposition_6_1_all_slices](ConditionalGoldbach/Proofs/SpectralConsequences.lean#L56)
- [proposition_6_1_complex_slice](ConditionalGoldbach/Proofs/SpectralConsequences.lean#L65)
- [proposition_6_5_diagonal_vector_spec](ConditionalGoldbach/Proofs/SpectralDiagonalVector.lean#L111)
- [theorem_6_1_abstract_dictionary](ConditionalGoldbach/Proofs/SpectralDictionary.lean#L166)
- [proposition_5_3_hs_basis_independent](ConditionalGoldbach/Proofs/SpectralHilbertSchmidt.lean#L52)
- [lemma_6_4_poisson_action_spec](ConditionalGoldbach/Proofs/SpectralPoisson.lean#L29)
- [lemma_6_4_perron_residue](ConditionalGoldbach/Proofs/SpectralPoisson.lean#L43)
- [lemma_6_4_poisson_convolution](ConditionalGoldbach/Proofs/SpectralPoissonConvolution.lean#L172)
- [proposition_6_1_positive_fredholm_spec](ConditionalGoldbach/Proofs/SpectralPositiveFredholm.lean#L17)
- [lemma_4_3_uniform](ConditionalGoldbach/Proofs/TotientLogLog.lean#L170)
- [proposition_A_2](ConditionalGoldbach/Proofs/VariableConsequences.lean#L19)
- [proposition_A_1](ConditionalGoldbach/Proofs/VariableQuadratic.lean#L55)
- [proposition_A_2_pointwise](ConditionalGoldbach/Proofs/VariableQuadratic.lean#L116)
- [proposition_A_1_operator_spec](ConditionalGoldbach/Proofs/VariableStripOperators.lean#L151)
- [theorem_1_1_weight_exists](ConditionalGoldbach/Proofs/Weights.lean#L45)
- [lemma_3_5_weight_support](ConditionalGoldbach/Proofs/Weights.lean#L66)
- [lemma_7_2_convolutions](ConditionalGoldbach/Proofs/Weights.lean#L115)
- [proposition_7_4_norm_integrals](ConditionalGoldbach/Proofs/Weights.lean#L196)
- [lemma_B_3](ConditionalGoldbach/Proofs/WideError.lean#L11)
- [lemma_B_3_main_integral](ConditionalGoldbach/Proofs/WideMainIntegral.lean#L65)
- [proposition_B_4](ConditionalGoldbach/Proofs/WideMellinResidual.lean#L58)
- [lemma_B_2](ConditionalGoldbach/Proofs/WideMoments.lean#L84)
- [proposition_B_1](ConditionalGoldbach/Proofs/WidePrimePowerCount.lean#L143)
- [proposition_B_4_weight](ConditionalGoldbach/Proofs/WideWeight.lean#L163)

## Pending reviewed declarations

- [Character](ConditionalGoldbach/BaseDefinitions.lean#L11): `definition`.
- [mangoldt](ConditionalGoldbach/BaseDefinitions.lean#L16): `definition`.
- [prime](ConditionalGoldbach/BaseDefinitions.lean#L18): `definition`.
- [IsWeight](ConditionalGoldbach/BaseDefinitions.lean#L20): `definition`.
- [companion](ConditionalGoldbach/BaseDefinitions.lean#L24): `definition`.
- [derivativeWeight](ConditionalGoldbach/BaseDefinitions.lean#L26): `definition`.
- [weightMass](ConditionalGoldbach/BaseDefinitions.lean#L29): `definition`.
- [C2](ConditionalGoldbach/BaseDefinitions.lean#L31): `definition`.
- [singularSeries](ConditionalGoldbach/BaseDefinitions.lean#L33): `definition`.
- [goldbach](ConditionalGoldbach/BaseDefinitions.lean#L36): `definition`.
- [diagonalMoment](ConditionalGoldbach/BaseDefinitions.lean#L42): `definition`.
- [oddCharacters](ConditionalGoldbach/BaseDefinitions.lean#L46): `definition`.
- [characterPolynomial](ConditionalGoldbach/BaseDefinitions.lean#L49): `definition`.
- [characterMoment](ConditionalGoldbach/BaseDefinitions.lean#L53): `definition`.
- [GRH](ConditionalGoldbach/BaseDefinitions.lean#L56): `definition`.
- [logDerivative](ConditionalGoldbach/BaseDefinitions.lean#L60): `definition`.
- [characterKernel](ConditionalGoldbach/BaseDefinitions.lean#L63): `definition`.
- [diagonalSeries](ConditionalGoldbach/BaseDefinitions.lean#L67): `definition`.
- [densitySeries](ConditionalGoldbach/BaseDefinitions.lean#L71): `definition`.
- [densityEulerProduct](ConditionalGoldbach/BaseDefinitions.lean#L74): `definition`.
- [continuedDensity](ConditionalGoldbach/BaseDefinitions.lean#L78): `definition`.
- [betaKernel](ConditionalGoldbach/BaseDefinitions.lean#L81): `definition`.
- [gammaQuotient](ConditionalGoldbach/BaseDefinitions.lean#L85): `definition`.
- [betaModel](ConditionalGoldbach/BaseDefinitions.lean#L88): `definition`.
- [continuedModel](ConditionalGoldbach/BaseDefinitions.lean#L91): `definition`.
- [residual](ConditionalGoldbach/BaseDefinitions.lean#L96): `definition`.
- [analyticDomain](ConditionalGoldbach/BaseDefinitions.lean#L99): `definition`.
- [betaDomain](ConditionalGoldbach/BaseDefinitions.lean#L102): `definition`.
- [alpha](ConditionalGoldbach/BaseDefinitions.lean#L105): `definition`.
- [beta](ConditionalGoldbach/BaseDefinitions.lean#L107): `definition`.
- [sigmaStar](ConditionalGoldbach/BaseDefinitions.lean#L109): `definition`.
- [width](ConditionalGoldbach/BaseDefinitions.lean#L111): `definition`.
- [strip](ConditionalGoldbach/BaseDefinitions.lean#L113): `definition`.
- [line](ConditionalGoldbach/BaseDefinitions.lean#L115): `definition`.
- [boundaryIntegral](ConditionalGoldbach/BaseDefinitions.lean#L117): `definition`.
- [mellinWeight](ConditionalGoldbach/BaseDefinitions.lean#L120): `definition`.
- [verticalMellin](ConditionalGoldbach/BaseDefinitions.lean#L123): `definition`.
- [residualIntegral](ConditionalGoldbach/BaseDefinitions.lean#L126): `definition`.
- [differenceConvolution](ConditionalGoldbach/BaseDefinitions.lean#L130): `definition`.
- [sumConvolution](ConditionalGoldbach/BaseDefinitions.lean#L133): `definition`.
- [signedConvolution](ConditionalGoldbach/BaseDefinitions.lean#L136): `definition`.
- [hardyWeight](ConditionalGoldbach/BaseDefinitions.lean#L139): `definition`.
- [hardyMeasure](ConditionalGoldbach/BaseDefinitions.lean#L141): `definition`.
- [HardySpace](ConditionalGoldbach/BaseDefinitions.lean#L144): `definition`.
- [fourierLaplace](ConditionalGoldbach/BaseDefinitions.lean#L146): `definition`.
- [IsRawHardy](ConditionalGoldbach/BaseDefinitions.lean#L149): `definition`.
- [rawHardyNormSq](ConditionalGoldbach/BaseDefinitions.lean#L156): `definition`.
- [interiorLine](ConditionalGoldbach/Definitions.lean#L17): `definition`.
- [IsBoundaryTrace](ConditionalGoldbach/Definitions.lean#L21): `definition`.
- [boundaryTraces](ConditionalGoldbach/Definitions.lean#L33): `definition`.
- [paperInner](ConditionalGoldbach/Definitions.lean#L36): `definition`.
- [weightedKernel](ConditionalGoldbach/Definitions.lean#L39): `definition`.
- [kernelAction](ConditionalGoldbach/Definitions.lean#L42): `definition`.
- [RepresentsKernel](ConditionalGoldbach/Definitions.lean#L47): `definition`.
- [kernelOperator](ConditionalGoldbach/Definitions.lean#L51): `definition`.
- [residualOperator](ConditionalGoldbach/Definitions.lean#L55): `definition`.
- [arithmeticOperator](ConditionalGoldbach/Definitions.lean#L58): `definition`.
- [diagonalOperator](ConditionalGoldbach/Definitions.lean#L61): `definition`.
- [modelOperator](ConditionalGoldbach/Definitions.lean#L64): `definition`.
- [IsHilbertSchmidt](ConditionalGoldbach/Definitions.lean#L67): `definition`.
- [hsNorm](ConditionalGoldbach/Definitions.lean#L71): `definition`.
- [IsPositiveTraceClass](ConditionalGoldbach/Definitions.lean#L76): `definition`.
- [positiveTrace](ConditionalGoldbach/Definitions.lean#L81): `definition`.
- [SpectralData](ConditionalGoldbach/Definitions.lean#L86): `definition`.
- [eigenvalues](ConditionalGoldbach/Definitions.lean#L93): `definition`.
- [spectralScale](ConditionalGoldbach/Definitions.lean#L97): `definition`.
- [spectralComplex](ConditionalGoldbach/Definitions.lean#L100): `definition`.
- [spectralPartialQuaternion](ConditionalGoldbach/Definitions.lean#L104): `definition`.
- [spectralQuaternion](ConditionalGoldbach/Definitions.lean#L109): `definition`.
- [RealizationValid](ConditionalGoldbach/Definitions.lean#L114): `definition`.
- [normFunctional](ConditionalGoldbach/Definitions.lean#L117): `definition`.
- [weightEnergy](ConditionalGoldbach/Definitions.lean#L122): `definition`.
- [functionalValue](ConditionalGoldbach/Definitions.lean#L125): `definition`.
- [rieszVector](ConditionalGoldbach/Definitions.lean#L129): `definition`.
- [evaluationVector](ConditionalGoldbach/Definitions.lean#L134): `definition`.
- [pointDistance](ConditionalGoldbach/Definitions.lean#L138): `definition`.
- [reproducingKernel](ConditionalGoldbach/Definitions.lean#L140): `definition`.
- [zeroFreeWidth](ConditionalGoldbach/Definitions.lean#L144): `definition`.
- [EvenEventually](ConditionalGoldbach/Definitions.lean#L147): `definition`.
- [EvenTendstoInfinity](ConditionalGoldbach/Definitions.lean#L149): `definition`.
- [IsAdmissible](ConditionalGoldbach/Definitions.lean#L152): `definition`.
- [SpectralR](ConditionalGoldbach/Definitions.lean#L156): `definition`.
- [SpectralZeroFree](ConditionalGoldbach/Definitions.lean#L159): `definition`.
- [HypothesisR](ConditionalGoldbach/Definitions.lean#L162): `definition`.
- [HypothesisS](ConditionalGoldbach/Definitions.lean#L165): `definition`.
- [PrimePairCount](ConditionalGoldbach/Definitions.lean#L169): `definition`.
- [ZeroIndex](ConditionalGoldbach/Definitions.lean#L173): `definition`.
- [completedL](ConditionalGoldbach/Definitions.lean#L177): `definition`.
- [zeroDifference](ConditionalGoldbach/Definitions.lean#L180): `definition`.
- [eulerCorrection](ConditionalGoldbach/Definitions.lean#L183): `definition`.
- [zeroPoisson](ConditionalGoldbach/Definitions.lean#L188): `definition`.
- [averagedLogDerivative](ConditionalGoldbach/Definitions.lean#L191): `definition`.
- [NormallySummableOn](ConditionalGoldbach/Definitions.lean#L195): `definition`.
- [HermitianKernel](ConditionalGoldbach/Definitions.lean#L201): `definition`.
- [PositiveKernel](ConditionalGoldbach/Definitions.lean#L203): `definition`.
- [BoundaryKernelSquareIntegral](ConditionalGoldbach/Definitions.lean#L207): `definition`.
- [IntrinsicEntire](ConditionalGoldbach/Definitions.lean#L211): `definition`.
- [CompactUniformLimit](ConditionalGoldbach/Definitions.lean#L216): `definition`.
- [EvenAsymptotic](ConditionalGoldbach/Definitions.lean#L221): `definition`.
- [spectralWidthFromBound](ConditionalGoldbach/Definitions.lean#L224): `definition`.
- [arithmeticExpansionTerm](ConditionalGoldbach/Definitions.lean#L227): `definition`.
- [zeroWindow](ConditionalGoldbach/Definitions.lean#L233): `definition`.
- [wirtingerBar](ConditionalGoldbach/Definitions.lean#L236): `definition`.
- [wirtinger](ConditionalGoldbach/Definitions.lean#L239): `definition`.
- [positiveFredholmDet](ConditionalGoldbach/Definitions.lean#L242): `definition`.
- [fredholmSquareDet](ConditionalGoldbach/Definitions.lean#L246): `definition`.
- [HypothesisRAt](ConditionalGoldbach/Definitions.lean#L250): `definition`.
- [HypothesisSAt](ConditionalGoldbach/Definitions.lean#L253): `definition`.
- [baselineBound](ConditionalGoldbach/Definitions.lean#L257): `definition`.
- [balanceFactor](ConditionalGoldbach/Definitions.lean#L259): `definition`.
- [poleCoefficient](ConditionalGoldbach/Definitions.lean#L261): `definition`.
- [experimentN](ConditionalGoldbach/Definitions.lean#L265): `definition`.
- [cutoffPolynomial](ConditionalGoldbach/Definitions.lean#L267): `definition`.
- [wideCutoff](ConditionalGoldbach/Definitions.lean#L271): `definition`.
- [wideCompanion](ConditionalGoldbach/Definitions.lean#L275): `definition`.
- [wideWeight](ConditionalGoldbach/Definitions.lean#L280): `definition`.
- [wideCorrelation](ConditionalGoldbach/Definitions.lean#L282): `definition`.
- [unorderedPrimePairs](ConditionalGoldbach/Definitions.lean#L284): `definition`.
- [edgeCorrection](ConditionalGoldbach/Definitions.lean#L287): `definition`.
- [primePowerCorrection](ConditionalGoldbach/Definitions.lean#L291): `definition`.
- [countingCoefficient](ConditionalGoldbach/Definitions.lean#L298): `definition`.
- [countingIntegral](ConditionalGoldbach/Definitions.lean#L300): `definition`.
- [diagonalCountingMoment](ConditionalGoldbach/Definitions.lean#L304): `definition`.
- [approxSignedMoment](ConditionalGoldbach/Definitions.lean#L307): `definition`.
- [approxDiagonalMoment](ConditionalGoldbach/Definitions.lean#L310): `definition`.
- [wideModelMass](ConditionalGoldbach/Definitions.lean#L313): `definition`.
- [wideResidual](ConditionalGoldbach/Definitions.lean#L315): `definition`.
- [approxPrimeCount](ConditionalGoldbach/Definitions.lean#L317): `definition`.
- [countError](ConditionalGoldbach/Definitions.lean#L320): `definition`.
- [wideFunctional](ConditionalGoldbach/Definitions.lean#L323): `definition`.
- [wideRieszVector](ConditionalGoldbach/Definitions.lean#L327): `definition`.
- [spectralNode](ConditionalGoldbach/Definitions.lean#L331): `definition`.
- [trapezoidWeight](ConditionalGoldbach/Definitions.lean#L334): `definition`.
- [finiteSpectralMatrix](ConditionalGoldbach/Definitions.lean#L337): `definition`.
- [finiteSpectralFunction](ConditionalGoldbach/Definitions.lean#L341): `definition`.
- [IsFiniteSpectrum](ConditionalGoldbach/Definitions.lean#L345): `definition`.
- [finiteEigenvalues](ConditionalGoldbach/Definitions.lean#L350): `definition`.
- [finiteMatrixOpNorm](ConditionalGoldbach/Definitions.lean#L353): `definition`.
- [betaGamma](ConditionalGoldbach/Definitions.lean#L357): `definition`.
- [BoundaryParameter](ConditionalGoldbach/Definitions.lean#L359): `definition`.
- [boundaryPoint](ConditionalGoldbach/Definitions.lean#L361): `definition`.
- [boundaryMeasure](ConditionalGoldbach/Definitions.lean#L364): `definition`.
- [positiveDifferenceFamily](ConditionalGoldbach/Definitions.lean#L367): `definition`.
- [negativeDifferenceFamily](ConditionalGoldbach/Definitions.lean#L370): `definition`.
- [sumFamily](ConditionalGoldbach/Definitions.lean#L373): `definition`.
- [pairedZeroSum](ConditionalGoldbach/Definitions.lean#L376): `definition`.
- [zeroMultiplicity](ConditionalGoldbach/Definitions.lean#L380): `definition`.
- [spectralRootParameter](ConditionalGoldbach/Definitions.lean#L383): `definition`.
- [quaternionSlice](ConditionalGoldbach/Definitions.lean#L386): `definition`.
- [complexQuaternion](ConditionalGoldbach/Definitions.lean#L389): `definition`.
- [fueterOperator](ConditionalGoldbach/Definitions.lean#L391): `definition`.
- [referenceLine](ConditionalGoldbach/Definitions.lean#L395): `definition`.
- [perronCutoff](ConditionalGoldbach/Definitions.lean#L397): `definition`.
- [smoothedPerronWeight](ConditionalGoldbach/Definitions.lean#L399): `definition`.
- [smoothedDirichletPolynomial](ConditionalGoldbach/Definitions.lean#L404): `definition`.
- [smoothedPerronKernel](ConditionalGoldbach/Definitions.lean#L408): `definition`.
- [logDerivativeEnergy](ConditionalGoldbach/Definitions.lean#L411): `definition`.
- [poissonKernelReal](ConditionalGoldbach/Definitions.lean#L414): `definition`.
- [realConvolution](ConditionalGoldbach/Definitions.lean#L416): `definition`.
- [poissonAction](ConditionalGoldbach/Definitions.lean#L419): `definition`.
- [diagonalVector](ConditionalGoldbach/Definitions.lean#L422): `definition`.
- [weightIntegral](ConditionalGoldbach/Definitions.lean#L424): `definition`.
- [functionalIntegrand](ConditionalGoldbach/Definitions.lean#L426): `definition`.
- [availableNormMajorant](ConditionalGoldbach/Definitions.lean#L429): `definition`.
- [baselineProductR](ConditionalGoldbach/Definitions.lean#L432): `definition`.
- [wideMainIntegral](ConditionalGoldbach/Definitions.lean#L438): `definition`.
- [HasMomentError](ConditionalGoldbach/Definitions.lean#L442): `definition`.
- [spectralPartialQuaternionReindexed](ConditionalGoldbach/Definitions.lean#L446): `definition`.
- [centeredSpectralPartial](ConditionalGoldbach/Definitions.lean#L452): `definition`.
- [diagonalHardyVector](ConditionalGoldbach/Definitions.lean#L459): `definition`.
- [localDensityFactor](ConditionalGoldbach/Definitions.lean#L464): `definition`.
