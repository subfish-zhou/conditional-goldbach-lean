# Conditional Goldbach: proof library

[Chinese](README.zh.md) · [Proof explorer](progress.html) · [Axiom ledger](proof-status.json)

Lean 4 proofs of the reviewed Li–Liu statements, including the analytic, Hardy-space, operator, and spectral constructions. The main theorems give asymptotics for sufficiently large even integers under GRH and spectral condition S or R, with the original quantifier order and constant dependencies.

## Current status

**102 of 102 reviewed declarations** have complete transitive proof dependencies. The ledger records 0 declarations with written proofs and pending dependencies, and 0 direct placeholders. Across all public theorems and auxiliary results, **1400** have complete proof dependencies.

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
lake --wfail build
python3 scripts/check_project.py
python3 scripts/check_public_api.py
python3 scripts/check_entrypoints.py
python3 scripts/audit_proofs.py
python3 scripts/check_reviewed_types.py
python3 scripts/check_definitions.py
python3 scripts/write_progress_report.py
python3 scripts/build_progress.py
```

The toolchain is Lean 4.35.0. Mathlib is pinned to `56a005855ea17e0b0958f73ec801ae140b0a1679`; the `goldbach-lean` Git dependency is pinned in `lakefile.toml` and `lake-manifest.json`. See [dependency details](../docs/dependencies.md).

HTML generation uses the optional packages in `requirements-review.txt` and `package.json`. The generated reports work offline.

See [choosing an import](../docs/imports.md) for isolated consumers and enforced dependency boundaries.

See the [development and public-interface guide](../docs/development.md) for daily checks, the complete release sequence and CI.

## Library map

| Modules | Content |
|---|---|
| `Definitions/*.lean` | Reviewed objects split into arithmetic, analytic, Hardy, Hilbert, spectral, and experiment modules |
| `BaseDefinitions.lean`, `Definitions.lean` | Compatibility entry points reexporting the original reviewed definitions |
| `Analysis/L2Fourier.lean` | Mathlib-only Fourier and L² dilation interfaces |
| `Analysis/SpectralData.lean` | Shared Hilbert coordinate and norm identities |
| `Proofs/HardyFourier.lean`, `Proofs/SpectralDataAlgebra.lean` | Compatibility entrypoints for the shared analysis interfaces |
| `Proofs/MellinDoubleDiagonal.lean` | Shared double-Mellin diagonalization and density-factor extraction |
| `Proofs/MellinBetaConvolutionCore.lean` | Shared Beta–Mellin convolution proofs with weight-specific wrappers |
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
- `verification/entrypoints.json`: isolated consumer exports, compiled import inventories, and dependency budgets.
- `verification/public-api.json`: all 1621 frozen public declaration types, including binder names, order and implicitness.
- `verification/proof-policy.json`: source reachability and scoped elaboration options.
- `verification.json`: consolidated build and verification records.
- [Independent source audit](verification/independent-audit/report.html): original-TeX review, representation bridges, and comparator results.

`reference/Reviewed.lean` preserves the earlier statement-review snapshot. The main library imports the completed proof modules. Audit challenges use placeholders to specify expected targets; their solutions provide the corresponding proofs.

## Completed reviewed declarations

- [interiorLine_memLp](ConditionalGoldbach/Definitions/HardyTraces.lean#L15)
- [boundaryTraces_exist](ConditionalGoldbach/Definitions/HardyTraces.lean#L31)
- [proposition_6_5_components_spec](ConditionalGoldbach/Proofs/ArithmeticComponentOperators.lean#L110)
- [lemma_A_3_balance](ConditionalGoldbach/Proofs/BalanceBounds.lean#L40)
- [lemma_A_3_width_ratio](ConditionalGoldbach/Proofs/BalanceBounds.lean#L97)
- [proposition_A_4_baseline_product](ConditionalGoldbach/Proofs/BaselineEuler.lean#L126)
- [lemma_4_2](ConditionalGoldbach/Proofs/BetaIdentity.lean#L224)
- [lemma_4_1](ConditionalGoldbach/Proofs/BetaIntegrals.lean#L177)
- [lemma_4_1_absolute_convergence](ConditionalGoldbach/Proofs/BetaIntegrals.lean#L188)
- [lemma_4_1_signed_model](ConditionalGoldbach/Proofs/BetaIntegrals.lean#L200)
- [lemma_4_2_meromorphic](ConditionalGoldbach/Proofs/BetaMeromorphic.lean#L133)
- [proposition_3_2](ConditionalGoldbach/Proofs/CharacterAnalytic.lean#L114)
- [lemma_6_4](ConditionalGoldbach/Proofs/CharacterAverage.lean#L84)
- [proposition_3_2_joint_meromorphic](ConditionalGoldbach/Proofs/CharacterJoint.lean#L59)
- [lemma_3_4_paired_zero_sum](ConditionalGoldbach/Proofs/CharacterSeries.lean#L66)
- [lemma_3_4](ConditionalGoldbach/Proofs/CharacterZeroExpansion.lean#L57)
- [lemma_3_4_normal_convergence](ConditionalGoldbach/Proofs/CharacterZeroShiftNormal.lean#L30)
- [lemma_6_4_zero_poisson_convergence](ConditionalGoldbach/Proofs/CharacterZeroSummability.lean#L126)
- [lemma_3_1_odd_orthogonality](ConditionalGoldbach/Proofs/Characters.lean#L65)
- [lemma_3_1](ConditionalGoldbach/Proofs/Characters.lean#L367)
- [lemma_4_3_density_convergence](ConditionalGoldbach/Proofs/DensityConvergence.lean#L79)
- [lemma_4_3_euler_product_convergence](ConditionalGoldbach/Proofs/DensityEuler.lean#L152)
- [lemma_4_3](ConditionalGoldbach/Proofs/DensityEulerIdentity.lean#L103)
- [theorem_6_1](ConditionalGoldbach/Proofs/DictionaryApplication.lean#L37)
- [singularSeries_eq_existing](ConditionalGoldbach/Proofs/Elementary.lean#L16)
- [proposition_B_5](ConditionalGoldbach/Proofs/FiniteExperimentSpectrum.lean#L152)
- [lemma_3_3](ConditionalGoldbach/Proofs/HadamardLimit.lean#L114)
- [proposition_5_3](ConditionalGoldbach/Proofs/HardyArithmeticTheorems.lean#L35)
- [proposition_5_4_kernel_pairing](ConditionalGoldbach/Proofs/HardyArithmeticTheorems.lean#L56)
- [proposition_5_3_kernel_integrability](ConditionalGoldbach/Proofs/HardyArithmeticTheorems.lean#L64)
- [proposition_5_4](ConditionalGoldbach/Proofs/HardyArithmeticTheorems.lean#L75)
- [proposition_5_4_fixed_contour](ConditionalGoldbach/Proofs/HardyArithmeticTheorems.lean#L88)
- [lemma_5_2](ConditionalGoldbach/Proofs/HardyConverse.lean#L45)
- [proposition_5_4_exact_norm](ConditionalGoldbach/Proofs/HardyReproducing.lean#L138)
- [lemma_5_2_representation_spec](ConditionalGoldbach/Proofs/HardyTraceAlgebra.lean#L126)
- [lemma_5_2_closed_trace_space](ConditionalGoldbach/Proofs/HardyTraceAlgebra.lean#L183)
- [lemma_5_2_boundary_inner](ConditionalGoldbach/Proofs/HardyTraceAlgebra.lean#L199)
- [proposition_3_2_finite_rank](ConditionalGoldbach/Proofs/KernelAlgebra.lean#L111)
- [proposition_5_1](ConditionalGoldbach/Proofs/KernelRegularity.lean#L101)
- [proposition_5_1_fueter_equation](ConditionalGoldbach/Proofs/KernelRegularity.lean#L150)
- [theorem_7_1_uniform](ConditionalGoldbach/Proofs/Main.lean#L17)
- [theorem_1_1](ConditionalGoldbach/Proofs/Main.lean#L57)
- [theorem_1_2](ConditionalGoldbach/Proofs/Main.lean#L101)
- [lemma_7_1](ConditionalGoldbach/Proofs/MellinCharacterShift.lean#L109)
- [lemma_7_1_absolute_convergence](ConditionalGoldbach/Proofs/MellinCharacterShift.lean#L155)
- [lemma_7_2](ConditionalGoldbach/Proofs/MellinModelDouble.lean#L27)
- [lemma_7_2_absolute_convergence](ConditionalGoldbach/Proofs/MellinModelDouble.lean#L38)
- [lemma_3_5](ConditionalGoldbach/Proofs/MellinMoment.lean#L101)
- [lemma_3_5_absolute_convergence](ConditionalGoldbach/Proofs/MellinMomentComplete.lean#L14)
- [lemma_3_5_small_sigma](ConditionalGoldbach/Proofs/MellinMomentComplete.lean#L25)
- [proposition_7_3](ConditionalGoldbach/Proofs/MellinResidual.lean#L92)
- [proposition_7_3_absolute_convergence](ConditionalGoldbach/Proofs/MellinResidual.lean#L101)
- [proposition_4_4](ConditionalGoldbach/Proofs/ModelContinuation.lean#L92)
- [proposition_A_4](ConditionalGoldbach/Proofs/PoleObstruction.lean#L15)
- [primePair_consequence](ConditionalGoldbach/Proofs/PrimePairs.lean#L17)
- [lemma_7_5](ConditionalGoldbach/Proofs/QuadraticEstimates.lean#L41)
- [lemma_7_5_asymptotic](ConditionalGoldbach/Proofs/QuadraticEstimates.lean#L78)
- [proposition_7_4](ConditionalGoldbach/Proofs/QuadraticFunctional.lean#L15)
- [theorem_7_1](ConditionalGoldbach/Proofs/QuadraticIdentity.lean#L121)
- [proposition_6_5](ConditionalGoldbach/Proofs/QuantitativeBounds.lean#L26)
- [lemma_A_3_absolute_operator_bound](ConditionalGoldbach/Proofs/QuantitativeBounds.lean#L45)
- [lemma_A_3](ConditionalGoldbach/Proofs/QuantitativeBounds.lean#L56)
- [theorem_6_2](ConditionalGoldbach/Proofs/QuantitativeBounds.lean#L111)
- [proposition_4_5](ConditionalGoldbach/Proofs/ResidualAnalytic.lean#L89)
- [lemma_4_1_local_density](ConditionalGoldbach/Proofs/SingularDensity.lean#L68)
- [theorem_1_2_hypothesisR_implies_S](ConditionalGoldbach/Proofs/SpectralAlgebra.lean#L16)
- [theorem_6_1_width_comparison](ConditionalGoldbach/Proofs/SpectralAlgebra.lean#L29)
- [proposition_6_3_factor_central_order](ConditionalGoldbach/Proofs/SpectralAlgebra.lean#L131)
- [proposition_6_2](ConditionalGoldbach/Proofs/SpectralCompletion.lean#L85)
- [proposition_6_1_spectral_choice_independent](ConditionalGoldbach/Proofs/SpectralCompletionChoice.lean#L108)
- [proposition_6_1_square_determinant](ConditionalGoldbach/Proofs/SpectralCompletionDeterminant.lean#L41)
- [proposition_6_1](ConditionalGoldbach/Proofs/SpectralCompletionDeterminant.lean#L50)
- [proposition_6_1_enumeration](ConditionalGoldbach/Proofs/SpectralCompletionIdentities.lean#L60)
- [proposition_6_2_centered_product](ConditionalGoldbach/Proofs/SpectralCompletionIdentities.lean#L105)
- [proposition_6_2_critical_values](ConditionalGoldbach/Proofs/SpectralCompletionIdentities.lean#L159)
- [proposition_6_3_multiplicities](ConditionalGoldbach/Proofs/SpectralCompletionMultiplicities.lean#L91)
- [proposition_6_3_three_cases](ConditionalGoldbach/Proofs/SpectralCompletionZeros.lean#L95)
- [proposition_6_3](ConditionalGoldbach/Proofs/SpectralConsequences.lean#L38)
- [proposition_6_1_all_slices](ConditionalGoldbach/Proofs/SpectralConsequences.lean#L61)
- [proposition_6_1_complex_slice](ConditionalGoldbach/Proofs/SpectralConsequences.lean#L70)
- [proposition_6_5_diagonal_vector_spec](ConditionalGoldbach/Proofs/SpectralDiagonalVector.lean#L114)
- [theorem_6_1_abstract_dictionary](ConditionalGoldbach/Proofs/SpectralDictionary.lean#L170)
- [proposition_5_3_hs_basis_independent](ConditionalGoldbach/Proofs/SpectralHilbertSchmidt.lean#L53)
- [lemma_6_4_poisson_action_spec](ConditionalGoldbach/Proofs/SpectralPoisson.lean#L35)
- [lemma_6_4_perron_residue](ConditionalGoldbach/Proofs/SpectralPoisson.lean#L49)
- [lemma_6_4_poisson_convolution](ConditionalGoldbach/Proofs/SpectralPoissonConvolution.lean#L175)
- [proposition_6_1_positive_fredholm_spec](ConditionalGoldbach/Proofs/SpectralPositiveFredholm.lean#L22)
- [lemma_4_3_uniform](ConditionalGoldbach/Proofs/TotientLogLog.lean#L173)
- [proposition_A_2](ConditionalGoldbach/Proofs/VariableConsequences.lean#L23)
- [proposition_A_1](ConditionalGoldbach/Proofs/VariableQuadratic.lean#L58)
- [proposition_A_2_pointwise](ConditionalGoldbach/Proofs/VariableQuadratic.lean#L120)
- [proposition_A_1_operator_spec](ConditionalGoldbach/Proofs/VariableStripOperators.lean#L159)
- [theorem_1_1_weight_exists](ConditionalGoldbach/Proofs/Weights.lean#L58)
- [lemma_3_5_weight_support](ConditionalGoldbach/Proofs/Weights.lean#L79)
- [lemma_7_2_convolutions](ConditionalGoldbach/Proofs/Weights.lean#L127)
- [proposition_7_4_norm_integrals](ConditionalGoldbach/Proofs/Weights.lean#L207)
- [lemma_B_3](ConditionalGoldbach/Proofs/WideError.lean#L14)
- [lemma_B_3_main_integral](ConditionalGoldbach/Proofs/WideMainIntegral.lean#L67)
- [proposition_B_4](ConditionalGoldbach/Proofs/WideMellinResidual.lean#L61)
- [lemma_B_2](ConditionalGoldbach/Proofs/WideMoments.lean#L86)
- [proposition_B_1](ConditionalGoldbach/Proofs/WidePrimePowerCount.lean#L145)
- [proposition_B_4_weight](ConditionalGoldbach/Proofs/WideWeight.lean#L165)

## Pending reviewed declarations

- [mangoldt](ConditionalGoldbach/Definitions/Arithmetic.lean#L16): `definition`.
- [prime](ConditionalGoldbach/Definitions/Arithmetic.lean#L18): `definition`.
- [C2](ConditionalGoldbach/Definitions/Arithmetic.lean#L20): `definition`.
- [singularSeries](ConditionalGoldbach/Definitions/Arithmetic.lean#L22): `definition`.
- [goldbach](ConditionalGoldbach/Definitions/Arithmetic.lean#L25): `definition`.
- [diagonalMoment](ConditionalGoldbach/Definitions/Arithmetic.lean#L31): `definition`.
- [PrimePairCount](ConditionalGoldbach/Definitions/Arithmetic.lean#L35): `definition`.
- [positiveDifferenceFamily](ConditionalGoldbach/Definitions/Arithmetic.lean#L39): `definition`.
- [negativeDifferenceFamily](ConditionalGoldbach/Definitions/Arithmetic.lean#L42): `definition`.
- [sumFamily](ConditionalGoldbach/Definitions/Arithmetic.lean#L45): `definition`.
- [localDensityFactor](ConditionalGoldbach/Definitions/Arithmetic.lean#L48): `definition`.
- [EvenEventually](ConditionalGoldbach/Definitions/Asymptotics.lean#L17): `definition`.
- [EvenTendstoInfinity](ConditionalGoldbach/Definitions/Asymptotics.lean#L19): `definition`.
- [NormallySummableOn](ConditionalGoldbach/Definitions/Asymptotics.lean#L22): `definition`.
- [HermitianKernel](ConditionalGoldbach/Definitions/Asymptotics.lean#L28): `definition`.
- [PositiveKernel](ConditionalGoldbach/Definitions/Asymptotics.lean#L30): `definition`.
- [BoundaryKernelSquareIntegral](ConditionalGoldbach/Definitions/Asymptotics.lean#L34): `definition`.
- [CompactUniformLimit](ConditionalGoldbach/Definitions/Asymptotics.lean#L38): `definition`.
- [EvenAsymptotic](ConditionalGoldbach/Definitions/Asymptotics.lean#L43): `definition`.
- [baselineBound](ConditionalGoldbach/Definitions/Asymptotics.lean#L46): `definition`.
- [balanceFactor](ConditionalGoldbach/Definitions/Asymptotics.lean#L48): `definition`.
- [availableNormMajorant](ConditionalGoldbach/Definitions/Asymptotics.lean#L50): `definition`.
- [boundaryIntegral](ConditionalGoldbach/Definitions/BoundaryIntegral.lean#L15): `definition`.
- [Character](ConditionalGoldbach/Definitions/Characters.lean#L19): `definition`.
- [oddCharacters](ConditionalGoldbach/Definitions/Characters.lean#L24): `definition`.
- [characterPolynomial](ConditionalGoldbach/Definitions/Characters.lean#L27): `definition`.
- [characterMoment](ConditionalGoldbach/Definitions/Characters.lean#L31): `definition`.
- [GRH](ConditionalGoldbach/Definitions/Characters.lean#L34): `definition`.
- [logDerivative](ConditionalGoldbach/Definitions/Characters.lean#L38): `definition`.
- [characterKernel](ConditionalGoldbach/Definitions/Characters.lean#L41): `definition`.
- [ZeroIndex](ConditionalGoldbach/Definitions/Characters.lean#L45): `definition`.
- [completedL](ConditionalGoldbach/Definitions/Characters.lean#L49): `definition`.
- [zeroDifference](ConditionalGoldbach/Definitions/Characters.lean#L52): `definition`.
- [eulerCorrection](ConditionalGoldbach/Definitions/Characters.lean#L55): `definition`.
- [zeroPoisson](ConditionalGoldbach/Definitions/Characters.lean#L60): `definition`.
- [averagedLogDerivative](ConditionalGoldbach/Definitions/Characters.lean#L63): `definition`.
- [arithmeticExpansionTerm](ConditionalGoldbach/Definitions/Characters.lean#L67): `definition`.
- [zeroWindow](ConditionalGoldbach/Definitions/Characters.lean#L73): `definition`.
- [poleCoefficient](ConditionalGoldbach/Definitions/Characters.lean#L76): `definition`.
- [pairedZeroSum](ConditionalGoldbach/Definitions/Characters.lean#L80): `definition`.
- [zeroMultiplicity](ConditionalGoldbach/Definitions/Characters.lean#L84): `definition`.
- [perronCutoff](ConditionalGoldbach/Definitions/Characters.lean#L87): `definition`.
- [smoothedPerronWeight](ConditionalGoldbach/Definitions/Characters.lean#L89): `definition`.
- [smoothedDirichletPolynomial](ConditionalGoldbach/Definitions/Characters.lean#L94): `definition`.
- [smoothedPerronKernel](ConditionalGoldbach/Definitions/Characters.lean#L98): `definition`.
- [logDerivativeEnergy](ConditionalGoldbach/Definitions/Characters.lean#L101): `definition`.
- [experimentN](ConditionalGoldbach/Definitions/Experiment.lean#L23): `definition`.
- [cutoffPolynomial](ConditionalGoldbach/Definitions/Experiment.lean#L25): `definition`.
- [wideCutoff](ConditionalGoldbach/Definitions/Experiment.lean#L29): `definition`.
- [wideCompanion](ConditionalGoldbach/Definitions/Experiment.lean#L33): `definition`.
- [wideWeight](ConditionalGoldbach/Definitions/Experiment.lean#L38): `definition`.
- [wideCorrelation](ConditionalGoldbach/Definitions/Experiment.lean#L40): `definition`.
- [unorderedPrimePairs](ConditionalGoldbach/Definitions/Experiment.lean#L42): `definition`.
- [edgeCorrection](ConditionalGoldbach/Definitions/Experiment.lean#L45): `definition`.
- [primePowerCorrection](ConditionalGoldbach/Definitions/Experiment.lean#L49): `definition`.
- [countingCoefficient](ConditionalGoldbach/Definitions/Experiment.lean#L56): `definition`.
- [countingIntegral](ConditionalGoldbach/Definitions/Experiment.lean#L58): `definition`.
- [diagonalCountingMoment](ConditionalGoldbach/Definitions/Experiment.lean#L62): `definition`.
- [approxSignedMoment](ConditionalGoldbach/Definitions/Experiment.lean#L65): `definition`.
- [approxDiagonalMoment](ConditionalGoldbach/Definitions/Experiment.lean#L68): `definition`.
- [wideModelMass](ConditionalGoldbach/Definitions/Experiment.lean#L71): `definition`.
- [wideResidual](ConditionalGoldbach/Definitions/Experiment.lean#L73): `definition`.
- [approxPrimeCount](ConditionalGoldbach/Definitions/Experiment.lean#L75): `definition`.
- [countError](ConditionalGoldbach/Definitions/Experiment.lean#L78): `definition`.
- [wideFunctional](ConditionalGoldbach/Definitions/Experiment.lean#L81): `definition`.
- [wideRieszVector](ConditionalGoldbach/Definitions/Experiment.lean#L85): `definition`.
- [wideMainIntegral](ConditionalGoldbach/Definitions/Experiment.lean#L89): `definition`.
- [HasMomentError](ConditionalGoldbach/Definitions/Experiment.lean#L93): `definition`.
- [spectralNode](ConditionalGoldbach/Definitions/FiniteSpectrum.lean#L18): `definition`.
- [trapezoidWeight](ConditionalGoldbach/Definitions/FiniteSpectrum.lean#L21): `definition`.
- [finiteSpectralMatrix](ConditionalGoldbach/Definitions/FiniteSpectrum.lean#L24): `definition`.
- [finiteSpectralFunction](ConditionalGoldbach/Definitions/FiniteSpectrum.lean#L28): `definition`.
- [IsFiniteSpectrum](ConditionalGoldbach/Definitions/FiniteSpectrum.lean#L32): `definition`.
- [finiteEigenvalues](ConditionalGoldbach/Definitions/FiniteSpectrum.lean#L37): `definition`.
- [finiteMatrixOpNorm](ConditionalGoldbach/Definitions/FiniteSpectrum.lean#L40): `definition`.
- [analyticDomain](ConditionalGoldbach/Definitions/GeometryCore.lean#L15): `definition`.
- [betaDomain](ConditionalGoldbach/Definitions/GeometryCore.lean#L18): `definition`.
- [alpha](ConditionalGoldbach/Definitions/GeometryCore.lean#L21): `definition`.
- [beta](ConditionalGoldbach/Definitions/GeometryCore.lean#L23): `definition`.
- [sigmaStar](ConditionalGoldbach/Definitions/GeometryCore.lean#L25): `definition`.
- [width](ConditionalGoldbach/Definitions/GeometryCore.lean#L27): `definition`.
- [strip](ConditionalGoldbach/Definitions/GeometryCore.lean#L29): `definition`.
- [line](ConditionalGoldbach/Definitions/GeometryCore.lean#L31): `definition`.
- [pointDistance](ConditionalGoldbach/Definitions/GeometryCore.lean#L33): `definition`.
- [referenceLine](ConditionalGoldbach/Definitions/GeometryCore.lean#L35): `definition`.
- [hardyWeight](ConditionalGoldbach/Definitions/Hardy.lean#L18): `definition`.
- [hardyMeasure](ConditionalGoldbach/Definitions/Hardy.lean#L20): `definition`.
- [HardySpace](ConditionalGoldbach/Definitions/Hardy.lean#L23): `definition`.
- [fourierLaplace](ConditionalGoldbach/Definitions/Hardy.lean#L25): `definition`.
- [IsRawHardy](ConditionalGoldbach/Definitions/Hardy.lean#L28): `definition`.
- [rawHardyNormSq](ConditionalGoldbach/Definitions/Hardy.lean#L35): `definition`.
- [reproducingKernel](ConditionalGoldbach/Definitions/Hardy.lean#L39): `definition`.
- [wirtingerBar](ConditionalGoldbach/Definitions/Hardy.lean#L43): `definition`.
- [wirtinger](ConditionalGoldbach/Definitions/Hardy.lean#L46): `definition`.
- [BoundaryParameter](ConditionalGoldbach/Definitions/Hardy.lean#L49): `definition`.
- [boundaryPoint](ConditionalGoldbach/Definitions/Hardy.lean#L51): `definition`.
- [boundaryMeasure](ConditionalGoldbach/Definitions/Hardy.lean#L54): `definition`.
- [poissonKernelReal](ConditionalGoldbach/Definitions/Hardy.lean#L57): `definition`.
- [realConvolution](ConditionalGoldbach/Definitions/Hardy.lean#L59): `definition`.
- [poissonAction](ConditionalGoldbach/Definitions/Hardy.lean#L62): `definition`.
- [diagonalVector](ConditionalGoldbach/Definitions/Hardy.lean#L65): `definition`.
- [interiorLine](ConditionalGoldbach/Definitions/HardyTraces.lean#L20): `definition`.
- [IsBoundaryTrace](ConditionalGoldbach/Definitions/HardyTraces.lean#L24): `definition`.
- [boundaryTraces](ConditionalGoldbach/Definitions/HardyTraces.lean#L36): `definition`.
- [paperInner](ConditionalGoldbach/Definitions/Hilbert.lean#L15): `definition`.
- [IsHilbertSchmidt](ConditionalGoldbach/Definitions/Hilbert.lean#L18): `definition`.
- [hsNorm](ConditionalGoldbach/Definitions/Hilbert.lean#L22): `definition`.
- [IsPositiveTraceClass](ConditionalGoldbach/Definitions/Hilbert.lean#L27): `definition`.
- [positiveTrace](ConditionalGoldbach/Definitions/Hilbert.lean#L32): `definition`.
- [SpectralData](ConditionalGoldbach/Definitions/Hilbert.lean#L37): `definition`.
- [eigenvalues](ConditionalGoldbach/Definitions/Hilbert.lean#L44): `definition`.
- [positiveFredholmDet](ConditionalGoldbach/Definitions/Hilbert.lean#L48): `definition`.
- [fredholmSquareDet](ConditionalGoldbach/Definitions/Hilbert.lean#L52): `definition`.
- [RealizationValid](ConditionalGoldbach/Definitions/Hypotheses.lean#L19): `definition`.
- [zeroFreeWidth](ConditionalGoldbach/Definitions/Hypotheses.lean#L22): `definition`.
- [IsAdmissible](ConditionalGoldbach/Definitions/Hypotheses.lean#L25): `definition`.
- [SpectralR](ConditionalGoldbach/Definitions/Hypotheses.lean#L29): `definition`.
- [SpectralZeroFree](ConditionalGoldbach/Definitions/Hypotheses.lean#L32): `definition`.
- [HypothesisR](ConditionalGoldbach/Definitions/Hypotheses.lean#L35): `definition`.
- [HypothesisS](ConditionalGoldbach/Definitions/Hypotheses.lean#L38): `definition`.
- [HypothesisRAt](ConditionalGoldbach/Definitions/Hypotheses.lean#L42): `definition`.
- [HypothesisSAt](ConditionalGoldbach/Definitions/Hypotheses.lean#L45): `definition`.
- [diagonalSeries](ConditionalGoldbach/Definitions/Model.lean#L18): `definition`.
- [densitySeries](ConditionalGoldbach/Definitions/Model.lean#L22): `definition`.
- [densityEulerProduct](ConditionalGoldbach/Definitions/Model.lean#L25): `definition`.
- [continuedDensity](ConditionalGoldbach/Definitions/Model.lean#L29): `definition`.
- [betaKernel](ConditionalGoldbach/Definitions/Model.lean#L32): `definition`.
- [gammaQuotient](ConditionalGoldbach/Definitions/Model.lean#L36): `definition`.
- [betaModel](ConditionalGoldbach/Definitions/Model.lean#L39): `definition`.
- [continuedModel](ConditionalGoldbach/Definitions/Model.lean#L42): `definition`.
- [residual](ConditionalGoldbach/Definitions/Model.lean#L47): `definition`.
- [residualIntegral](ConditionalGoldbach/Definitions/Model.lean#L50): `definition`.
- [betaGamma](ConditionalGoldbach/Definitions/Model.lean#L54): `definition`.
- [baselineProductR](ConditionalGoldbach/Definitions/Model.lean#L56): `definition`.
- [weightedKernel](ConditionalGoldbach/Definitions/Operators.lean#L19): `definition`.
- [kernelAction](ConditionalGoldbach/Definitions/Operators.lean#L22): `definition`.
- [RepresentsKernel](ConditionalGoldbach/Definitions/Operators.lean#L27): `definition`.
- [kernelOperator](ConditionalGoldbach/Definitions/Operators.lean#L31): `definition`.
- [residualOperator](ConditionalGoldbach/Definitions/Operators.lean#L35): `definition`.
- [arithmeticOperator](ConditionalGoldbach/Definitions/Operators.lean#L38): `definition`.
- [diagonalOperator](ConditionalGoldbach/Definitions/Operators.lean#L41): `definition`.
- [modelOperator](ConditionalGoldbach/Definitions/Operators.lean#L44): `definition`.
- [functionalValue](ConditionalGoldbach/Definitions/Operators.lean#L47): `definition`.
- [rieszVector](ConditionalGoldbach/Definitions/Operators.lean#L51): `definition`.
- [evaluationVector](ConditionalGoldbach/Definitions/Operators.lean#L56): `definition`.
- [diagonalHardyVector](ConditionalGoldbach/Definitions/Operators.lean#L60): `definition`.
- [spectralScale](ConditionalGoldbach/Definitions/Spectral.lean#L20): `definition`.
- [spectralComplex](ConditionalGoldbach/Definitions/Spectral.lean#L23): `definition`.
- [spectralPartialQuaternion](ConditionalGoldbach/Definitions/Spectral.lean#L27): `definition`.
- [spectralQuaternion](ConditionalGoldbach/Definitions/Spectral.lean#L32): `definition`.
- [IntrinsicEntire](ConditionalGoldbach/Definitions/Spectral.lean#L37): `definition`.
- [spectralWidthFromBound](ConditionalGoldbach/Definitions/Spectral.lean#L42): `definition`.
- [spectralRootParameter](ConditionalGoldbach/Definitions/Spectral.lean#L45): `definition`.
- [quaternionSlice](ConditionalGoldbach/Definitions/Spectral.lean#L48): `definition`.
- [complexQuaternion](ConditionalGoldbach/Definitions/Spectral.lean#L51): `definition`.
- [fueterOperator](ConditionalGoldbach/Definitions/Spectral.lean#L53): `definition`.
- [spectralPartialQuaternionReindexed](ConditionalGoldbach/Definitions/Spectral.lean#L57): `definition`.
- [centeredSpectralPartial](ConditionalGoldbach/Definitions/Spectral.lean#L63): `definition`.
- [IsWeight](ConditionalGoldbach/Definitions/Weights.lean#L17): `definition`.
- [companion](ConditionalGoldbach/Definitions/Weights.lean#L21): `definition`.
- [derivativeWeight](ConditionalGoldbach/Definitions/Weights.lean#L23): `definition`.
- [weightMass](ConditionalGoldbach/Definitions/Weights.lean#L26): `definition`.
- [mellinWeight](ConditionalGoldbach/Definitions/Weights.lean#L28): `definition`.
- [verticalMellin](ConditionalGoldbach/Definitions/Weights.lean#L31): `definition`.
- [differenceConvolution](ConditionalGoldbach/Definitions/Weights.lean#L34): `definition`.
- [sumConvolution](ConditionalGoldbach/Definitions/Weights.lean#L37): `definition`.
- [signedConvolution](ConditionalGoldbach/Definitions/Weights.lean#L40): `definition`.
- [normFunctional](ConditionalGoldbach/Definitions/Weights.lean#L43): `definition`.
- [weightEnergy](ConditionalGoldbach/Definitions/Weights.lean#L48): `definition`.
- [weightIntegral](ConditionalGoldbach/Definitions/Weights.lean#L51): `definition`.
- [functionalIntegrand](ConditionalGoldbach/Definitions/Weights.lean#L53): `definition`.
