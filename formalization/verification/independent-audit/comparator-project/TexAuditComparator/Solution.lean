import TexAuditComparator.Reference14
import TexAuditComparator.Reference57
import TexAuditComparator.ReferenceAB
import TexAuditComparator.Bridges14
import TexAuditComparator.Bridges57
import TexAuditComparator.NumericCrossCheck

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
universe u
namespace TexComparator

theorem statement_000_singularSeries_eq_existing : TexAudit14.expect_singularSeries_eq_existing := by
  exact @ConditionalGoldbach.singularSeries_eq_existing

theorem statement_001_theorem_1_1 : TexAudit14.expect_theorem_1_1 := by
  exact @ConditionalGoldbach.theorem_1_1

theorem statement_002_theorem_1_1_weight_exists : TexAudit14.expect_theorem_1_1_weight_exists := by
  exact @ConditionalGoldbach.theorem_1_1_weight_exists

theorem statement_003_theorem_1_2 : TexAudit14.expect_theorem_1_2 := by
  exact @ConditionalGoldbach.theorem_1_2

theorem statement_004_theorem_1_2_hypothesisR_implies_S : TexAudit14.expect_theorem_1_2_hypothesisR_implies_S := by
  exact @ConditionalGoldbach.theorem_1_2_hypothesisR_implies_S

theorem statement_005_primePair_consequence : TexAudit14.expect_primePair_consequence := by
  exact @ConditionalGoldbach.primePair_consequence

theorem statement_006_lemma_3_1 : TexAudit14.expect_lemma_3_1 := by
  exact @ConditionalGoldbach.lemma_3_1

theorem statement_007_lemma_3_1_odd_orthogonality : TexAudit14.expect_lemma_3_1_odd_orthogonality := by
  exact @ConditionalGoldbach.lemma_3_1_odd_orthogonality

theorem statement_008_proposition_3_2 : TexAudit14.expect_proposition_3_2 := by
  exact @ConditionalGoldbach.proposition_3_2

theorem statement_009_proposition_3_2_finite_rank : TexAudit14.expect_proposition_3_2_finite_rank := by
  exact @ConditionalGoldbach.proposition_3_2_finite_rank

theorem statement_010_proposition_3_2_joint_meromorphic : TexAudit14.expect_proposition_3_2_joint_meromorphic := by
  exact @ConditionalGoldbach.proposition_3_2_joint_meromorphic

theorem statement_011_lemma_3_3 : TexAudit14.expect_lemma_3_3 := by
  exact @ConditionalGoldbach.lemma_3_3

theorem statement_012_lemma_3_4 : TexAudit14.expect_lemma_3_4 := by
  exact @ConditionalGoldbach.lemma_3_4

theorem statement_013_lemma_3_4_normal_convergence : TexAudit14.expect_lemma_3_4_normal_convergence := by
  exact @ConditionalGoldbach.lemma_3_4_normal_convergence

theorem statement_014_lemma_3_4_paired_zero_sum : TexAudit14.expect_lemma_3_4_paired_zero_sum := by
  exact @ConditionalGoldbach.lemma_3_4_paired_zero_sum

theorem statement_015_lemma_3_5 : TexAudit14.expect_lemma_3_5 := by
  exact @ConditionalGoldbach.lemma_3_5

theorem statement_016_lemma_3_5_absolute_convergence : TexAudit14.expect_lemma_3_5_absolute_convergence := by
  exact @ConditionalGoldbach.lemma_3_5_absolute_convergence

theorem statement_017_lemma_3_5_small_sigma : TexAudit14.expect_lemma_3_5_small_sigma := by
  exact @ConditionalGoldbach.lemma_3_5_small_sigma

theorem statement_018_lemma_3_5_weight_support : TexAudit14.expect_lemma_3_5_weight_support := by
  exact @ConditionalGoldbach.lemma_3_5_weight_support

theorem statement_019_lemma_4_1 : TexAudit14.expect_lemma_4_1 := by
  exact @ConditionalGoldbach.lemma_4_1

theorem statement_020_lemma_4_1_absolute_convergence : TexAudit14.expect_lemma_4_1_absolute_convergence := by
  exact @ConditionalGoldbach.lemma_4_1_absolute_convergence

theorem statement_021_lemma_4_1_signed_model : TexAudit14.expect_lemma_4_1_signed_model := by
  exact @ConditionalGoldbach.lemma_4_1_signed_model

theorem statement_022_lemma_4_1_local_density : TexAudit14.expect_lemma_4_1_local_density := by
  exact @ConditionalGoldbach.lemma_4_1_local_density

theorem statement_023_lemma_4_2 : TexAudit14.expect_lemma_4_2 := by
  exact @ConditionalGoldbach.lemma_4_2

theorem statement_024_lemma_4_2_meromorphic : TexAudit14.expect_lemma_4_2_meromorphic := by
  exact @ConditionalGoldbach.lemma_4_2_meromorphic

theorem statement_025_lemma_4_3 : TexAudit14.expect_lemma_4_3 := by
  exact @ConditionalGoldbach.lemma_4_3

theorem statement_026_lemma_4_3_uniform : TexAudit14.expect_lemma_4_3_uniform := by
  exact @ConditionalGoldbach.lemma_4_3_uniform

theorem statement_027_lemma_4_3_density_convergence : TexAudit14.expect_lemma_4_3_density_convergence := by
  exact @ConditionalGoldbach.lemma_4_3_density_convergence

theorem statement_028_lemma_4_3_euler_product_convergence : TexAudit14.expect_lemma_4_3_euler_product_convergence := by
  exact @ConditionalGoldbach.lemma_4_3_euler_product_convergence

theorem statement_029_proposition_4_4 : TexAudit14.expect_proposition_4_4 := by
  exact @ConditionalGoldbach.proposition_4_4

theorem statement_030_proposition_4_5 : TexAudit14.expect_proposition_4_5 := by
  exact @ConditionalGoldbach.proposition_4_5

theorem statement_031_proposition_5_1 : TexAudit57.Expected_5_1 := by
  exact @ConditionalGoldbach.proposition_5_1

theorem statement_032_proposition_5_1_fueter_equation : TexAudit57.expect_proposition_5_1_fueter_equation := by
  exact @ConditionalGoldbach.proposition_5_1_fueter_equation

theorem statement_033_lemma_5_2 : TexAudit57.Expected_5_2 := by
  exact @ConditionalGoldbach.lemma_5_2

theorem statement_034_lemma_5_2_closed_trace_space : TexAudit57.expect_lemma_5_2_closed_trace_space := by
  exact @ConditionalGoldbach.lemma_5_2_closed_trace_space

theorem statement_035_lemma_5_2_representation_spec : TexAudit57.expect_lemma_5_2_representation_spec := by
  exact @ConditionalGoldbach.lemma_5_2_representation_spec

theorem statement_036_lemma_5_2_boundary_inner : TexAudit57.expect_lemma_5_2_boundary_inner := by
  exact @ConditionalGoldbach.lemma_5_2_boundary_inner

theorem statement_037_proposition_5_3 : TexAudit57.Expected_5_3 := by
  exact @ConditionalGoldbach.proposition_5_3

theorem statement_038_proposition_5_3_kernel_integrability : TexAudit57.expect_proposition_5_3_kernel_integrability := by
  exact @ConditionalGoldbach.proposition_5_3_kernel_integrability

theorem statement_039_proposition_5_3_hs_basis_independent : TexAudit57.expect_proposition_5_3_hs_basis_independent.{u} := by
  exact @ConditionalGoldbach.proposition_5_3_hs_basis_independent

theorem statement_040_proposition_5_4 : TexAudit57.Expected_5_4 := by
  exact @ConditionalGoldbach.proposition_5_4

theorem statement_041_proposition_5_4_exact_norm : TexAudit57.expect_proposition_5_4_exact_norm := by
  exact @ConditionalGoldbach.proposition_5_4_exact_norm

theorem statement_042_proposition_5_4_kernel_pairing : TexAudit57.expect_proposition_5_4_kernel_pairing := by
  exact @ConditionalGoldbach.proposition_5_4_kernel_pairing

theorem statement_043_proposition_5_4_fixed_contour : TexAudit57.expect_proposition_5_4_fixed_contour := by
  exact @ConditionalGoldbach.proposition_5_4_fixed_contour

theorem statement_044_proposition_6_1 : TexAudit57.Expected_6_1_product := by
  exact @ConditionalGoldbach.proposition_6_1

theorem statement_045_proposition_6_1_enumeration : TexAudit57.expect_proposition_6_1_enumeration := by
  exact @ConditionalGoldbach.proposition_6_1_enumeration

theorem statement_046_proposition_6_1_complex_slice : TexAudit57.expect_proposition_6_1_complex_slice := by
  exact @ConditionalGoldbach.proposition_6_1_complex_slice

theorem statement_047_proposition_6_1_positive_fredholm_spec : TexAudit57.expect_proposition_6_1_positive_fredholm_spec.{u} := by
  exact @ConditionalGoldbach.proposition_6_1_positive_fredholm_spec

theorem statement_048_proposition_6_1_square_determinant : TexAudit57.expect_proposition_6_1_square_determinant := by
  exact @ConditionalGoldbach.proposition_6_1_square_determinant

theorem statement_049_proposition_6_1_all_slices : TexAudit57.expect_proposition_6_1_all_slices := by
  exact @ConditionalGoldbach.proposition_6_1_all_slices

theorem statement_050_proposition_6_1_spectral_choice_independent : TexAudit57.expect_proposition_6_1_spectral_choice_independent.{u} := by
  exact @ConditionalGoldbach.proposition_6_1_spectral_choice_independent

theorem statement_051_proposition_6_2 : TexAudit57.Expected_6_2_symmetries := by
  exact @ConditionalGoldbach.proposition_6_2

theorem statement_052_proposition_6_2_centered_product : TexAudit57.expect_proposition_6_2_centered_product := by
  exact @ConditionalGoldbach.proposition_6_2_centered_product

theorem statement_053_proposition_6_2_critical_values : TexAudit57.expect_proposition_6_2_critical_values := by
  exact @ConditionalGoldbach.proposition_6_2_critical_values

theorem statement_054_proposition_6_3 : TexAudit57.Expected_6_3_zeros := by
  exact @ConditionalGoldbach.proposition_6_3

theorem statement_055_proposition_6_3_three_cases : TexAudit57.expect_proposition_6_3_three_cases := by
  exact @ConditionalGoldbach.proposition_6_3_three_cases

theorem statement_056_proposition_6_3_factor_central_order : TexAudit57.expect_proposition_6_3_factor_central_order := by
  exact @ConditionalGoldbach.proposition_6_3_factor_central_order

theorem statement_057_proposition_6_3_multiplicities : TexAudit57.expect_proposition_6_3_multiplicities := by
  exact @ConditionalGoldbach.proposition_6_3_multiplicities

theorem statement_058_theorem_6_1 : TexAudit57.Expected_6_1_dictionary := by
  exact @ConditionalGoldbach.theorem_6_1

theorem statement_059_theorem_6_1_abstract_dictionary : TexAudit57.expect_theorem_6_1_abstract_dictionary.{u} := by
  exact @ConditionalGoldbach.theorem_6_1_abstract_dictionary

theorem statement_060_theorem_6_1_width_comparison : TexAudit57.expect_theorem_6_1_width_comparison := by
  exact @ConditionalGoldbach.theorem_6_1_width_comparison

theorem statement_061_theorem_6_2 : TexAudit57.Expected_6_2_baseline := by
  exact @ConditionalGoldbach.theorem_6_2

theorem statement_062_lemma_6_4 : TexAudit57.Expected_6_4 := by
  exact @ConditionalGoldbach.lemma_6_4

theorem statement_063_lemma_6_4_zero_poisson_convergence : TexAudit57.expect_lemma_6_4_zero_poisson_convergence := by
  exact @ConditionalGoldbach.lemma_6_4_zero_poisson_convergence

theorem statement_064_lemma_6_4_perron_residue : TexAudit57.expect_lemma_6_4_perron_residue := by
  exact @ConditionalGoldbach.lemma_6_4_perron_residue

theorem statement_065_lemma_6_4_poisson_action_spec : TexAudit57.expect_lemma_6_4_poisson_action_spec := by
  exact @ConditionalGoldbach.lemma_6_4_poisson_action_spec

theorem statement_066_lemma_6_4_poisson_convolution : TexAudit57.expect_lemma_6_4_poisson_convolution := by
  exact @ConditionalGoldbach.lemma_6_4_poisson_convolution

theorem statement_067_proposition_6_5 : TexAudit57.Expected_6_5 := by
  exact @ConditionalGoldbach.proposition_6_5

theorem statement_068_proposition_6_5_components_spec : TexAudit57.expect_proposition_6_5_components_spec := by
  exact @ConditionalGoldbach.proposition_6_5_components_spec

theorem statement_069_proposition_6_5_diagonal_vector_spec : TexAudit57.expect_proposition_6_5_diagonal_vector_spec := by
  exact @ConditionalGoldbach.proposition_6_5_diagonal_vector_spec

theorem statement_070_lemma_7_1 : TexAudit57.Expected_7_1_mellin := by
  exact @ConditionalGoldbach.lemma_7_1

theorem statement_071_lemma_7_1_absolute_convergence : TexAudit57.expect_lemma_7_1_absolute_convergence := by
  exact @ConditionalGoldbach.lemma_7_1_absolute_convergence

theorem statement_072_lemma_7_2 : TexAudit57.Expected_7_2 := by
  exact @ConditionalGoldbach.lemma_7_2

theorem statement_073_lemma_7_2_absolute_convergence : TexAudit57.expect_lemma_7_2_absolute_convergence := by
  exact @ConditionalGoldbach.lemma_7_2_absolute_convergence

theorem statement_074_lemma_7_2_convolutions : TexAudit57.expect_lemma_7_2_convolutions := by
  exact @ConditionalGoldbach.lemma_7_2_convolutions

theorem statement_075_proposition_7_3 : TexAudit57.Expected_7_3 := by
  exact @ConditionalGoldbach.proposition_7_3

theorem statement_076_proposition_7_3_absolute_convergence : TexAudit57.expect_proposition_7_3_absolute_convergence := by
  exact @ConditionalGoldbach.proposition_7_3_absolute_convergence

theorem statement_077_proposition_7_4 : TexAudit57.Expected_7_4 := by
  exact @ConditionalGoldbach.proposition_7_4

theorem statement_078_proposition_7_4_norm_integrals : TexAudit57.expect_proposition_7_4_norm_integrals := by
  exact @ConditionalGoldbach.proposition_7_4_norm_integrals

theorem statement_079_theorem_7_1 : TexAudit57.Expected_7_1_quadratic := by
  exact @ConditionalGoldbach.theorem_7_1

theorem statement_080_theorem_7_1_uniform : TexAudit57.expect_theorem_7_1_uniform := by
  exact @ConditionalGoldbach.theorem_7_1_uniform

theorem statement_081_lemma_7_5 : TexAudit57.Expected_7_5 := by
  exact @ConditionalGoldbach.lemma_7_5

theorem statement_082_lemma_7_5_asymptotic : TexAudit57.expect_lemma_7_5_asymptotic := by
  exact @ConditionalGoldbach.lemma_7_5_asymptotic

theorem statement_083_interiorLine_memLp : TexAudit57.expect_interiorLine_memLp := by
  exact @ConditionalGoldbach.interiorLine_memLp

theorem statement_084_boundaryTraces_exist : TexAudit57.expect_boundaryTraces_exist := by
  exact @ConditionalGoldbach.boundaryTraces_exist

theorem statement_085_proposition_A_1 : TexAuditAB.A1 := by
  exact @ConditionalGoldbach.proposition_A_1

theorem statement_086_proposition_A_1_operator_spec : TexAuditAB.A1_operator := by
  exact @ConditionalGoldbach.proposition_A_1_operator_spec

theorem statement_087_proposition_A_2 : TexAuditAB.A2 := by
  exact @ConditionalGoldbach.proposition_A_2

theorem statement_088_proposition_A_2_pointwise : TexAuditAB.A2_pointwise := by
  exact @ConditionalGoldbach.proposition_A_2_pointwise

theorem statement_089_variable_uniform_spectral_bound : TexAuditAB.A2_uniform := by
  exact @ConditionalGoldbach.variable_uniform_spectral_bound

theorem statement_090_lemma_A_3 : TexAuditAB.A3 := by
  exact @ConditionalGoldbach.lemma_A_3

theorem statement_091_lemma_A_3_absolute_operator_bound : TexAuditAB.A3_absolute := by
  exact @ConditionalGoldbach.lemma_A_3_absolute_operator_bound

theorem statement_092_lemma_A_3_balance : TexAuditAB.A3_balance := by
  exact @ConditionalGoldbach.lemma_A_3_balance

theorem statement_093_lemma_A_3_width_ratio : TexAuditAB.A3_widths := by
  exact @ConditionalGoldbach.lemma_A_3_width_ratio

theorem statement_094_proposition_A_4 : TexAuditAB.A4 := by
  exact @ConditionalGoldbach.proposition_A_4

theorem statement_095_proposition_A_4_baseline_product : TexAuditAB.A4_regular := by
  exact @ConditionalGoldbach.proposition_A_4_baseline_product

theorem statement_096_proposition_B_1 : TexAuditAB.B1 := by
  exact @ConditionalGoldbach.proposition_B_1

theorem statement_097_lemma_B_2 : TexAuditAB.B2 := by
  exact @ConditionalGoldbach.lemma_B_2

theorem statement_098_lemma_B_3 : TexAuditAB.B3 := by
  exact @ConditionalGoldbach.lemma_B_3

theorem statement_099_lemma_B_3_main_integral : TexAuditAB.B3_main := by
  exact @ConditionalGoldbach.lemma_B_3_main_integral

theorem statement_100_proposition_B_4 : TexAuditAB.B4 := by
  exact @ConditionalGoldbach.proposition_B_4

theorem statement_101_proposition_B_4_weight : TexAuditAB.B4_weight := by
  exact @ConditionalGoldbach.proposition_B_4_weight

theorem statement_102_proposition_B_5 : TexAuditAB.B5 := by
  exact @ConditionalGoldbach.proposition_B_5

theorem definition_000_IsWeight : @TexAudit14.Weight = @ConditionalGoldbach.IsWeight := rfl

theorem definition_001_weightMass : @TexAudit14.Mass = @ConditionalGoldbach.weightMass := rfl

theorem definition_002_goldbach : @TexAudit14.Goldbach = @ConditionalGoldbach.goldbach := rfl

theorem definition_003_GRH : @TexAudit14.GRHExpected = @ConditionalGoldbach.GRH := rfl

theorem definition_004_EvenEventually : @TexAudit14.EventuallyEven = @ConditionalGoldbach.EvenEventually := rfl

theorem definition_005_EvenTendstoInfinity : @TexAudit14.TendsToInfinityEven = @ConditionalGoldbach.EvenTendstoInfinity := rfl

theorem definition_006_EvenAsymptotic : @TexAudit14.AsymptoticEven = @ConditionalGoldbach.EvenAsymptotic := rfl

theorem definition_007_zeroFreeWidth : @TexAudit14.Width = @ConditionalGoldbach.zeroFreeWidth := rfl

theorem definition_008_IsAdmissible : @TexAudit14.Admissible = @ConditionalGoldbach.IsAdmissible := rfl

theorem definition_009_HypothesisS : @TexAudit14.S = @ConditionalGoldbach.HypothesisS := rfl

theorem definition_010_HypothesisR : @TexAudit14.R = @ConditionalGoldbach.HypothesisR := rfl

theorem definition_011_spectralScale : @TexAudit14.Scale = @ConditionalGoldbach.spectralScale := rfl

theorem definition_012_PrimePairCount : @TexAudit14.PrimeCount = @ConditionalGoldbach.PrimePairCount := rfl

theorem definition_013_betaDomain : @TexAudit14.BetaRegion = @ConditionalGoldbach.betaDomain := rfl

theorem definition_014_analyticDomain : @TexAudit14.Omega = @ConditionalGoldbach.analyticDomain := rfl

theorem definition_015_betaKernel : @TexAudit14.BetaSigned = @ConditionalGoldbach.betaKernel := rfl

theorem definition_016_gammaQuotient : @TexAudit14.GammaRatio = @ConditionalGoldbach.gammaQuotient := rfl

theorem definition_017_densityEulerProduct : @TexAudit14.DensityProduct = @ConditionalGoldbach.densityEulerProduct := rfl

theorem definition_018_continuedDensity : @TexAudit14.ContinuedDensity = @ConditionalGoldbach.continuedDensity := rfl

theorem definition_019_betaModel : @TexAudit14.Model = @ConditionalGoldbach.betaModel := rfl

theorem definition_020_continuedModel : @TexAudit14.ContinuedModel = @ConditionalGoldbach.continuedModel := rfl

theorem definition_021_residual : @TexAudit14.Residual = @ConditionalGoldbach.residual := rfl

theorem definition_022_IsRawHardy : @TexAudit57.RawHardy = @ConditionalGoldbach.IsRawHardy := rfl

theorem definition_023_rawHardyNormSq : @TexAudit57.RawNormSquared = @ConditionalGoldbach.rawHardyNormSq := rfl

theorem definition_024_fourierLaplace : @TexAudit57.PW = @ConditionalGoldbach.fourierLaplace := rfl

theorem definition_025_IsBoundaryTrace : @TexAudit57.TracePair = @ConditionalGoldbach.IsBoundaryTrace := rfl

theorem definition_026_weightedKernel : @TexAudit57.WeightedResidual = @ConditionalGoldbach.weightedKernel := rfl

theorem definition_027_reproducingKernel : @TexAudit57.Reproducer = @ConditionalGoldbach.reproducingKernel := rfl

theorem definition_028_pointDistance : @TexAudit57.Distance = @ConditionalGoldbach.pointDistance := rfl

theorem definition_029_spectralRootParameter : @TexAudit57.RootRatio = @ConditionalGoldbach.spectralRootParameter := rfl

theorem definition_030_quaternionSlice : @TexAudit57.Slice = @ConditionalGoldbach.quaternionSlice := rfl

theorem definition_031_IntrinsicEntire : @TexAudit57.SliceEntire = @ConditionalGoldbach.IntrinsicEntire := rfl

theorem definition_032_zeroPoisson : @TexAudit57.ZeroSum = @ConditionalGoldbach.zeroPoisson := rfl

theorem definition_033_logDerivativeEnergy : @TexAudit57.Energy = @ConditionalGoldbach.logDerivativeEnergy := rfl

theorem definition_034_averagedLogDerivative : @TexAudit57.AverageEnergy = @ConditionalGoldbach.averagedLogDerivative := rfl

theorem definition_035_referenceLine : @TexAudit57.ReferenceLine = @ConditionalGoldbach.referenceLine := rfl

theorem definition_036_smoothedPerronWeight : @TexAudit57.Cutoff = @ConditionalGoldbach.smoothedPerronWeight := rfl

theorem definition_037_smoothedPerronKernel : @TexAudit57.Perron = @ConditionalGoldbach.smoothedPerronKernel := rfl

theorem definition_038_poissonKernelReal : @TexAudit57.Poisson = @ConditionalGoldbach.poissonKernelReal := rfl

theorem definition_039_realConvolution : @TexAudit57.Convolution = @ConditionalGoldbach.realConvolution := rfl

theorem definition_040_diagonalVector : @TexAudit57.DiagonalVector = @ConditionalGoldbach.diagonalVector := rfl

theorem definition_041_differenceConvolution : @TexAudit57.Difference = @ConditionalGoldbach.differenceConvolution := rfl

theorem definition_042_sumConvolution : @TexAudit57.SumOnPositiveHalfLine = @ConditionalGoldbach.sumConvolution := rfl

theorem definition_043_signedConvolution : @TexAudit57.Signed = @ConditionalGoldbach.signedConvolution := rfl

theorem definition_044_derivativeWeight : @TexAudit57.V = @ConditionalGoldbach.derivativeWeight := rfl

theorem definition_045_normFunctional : @TexAudit57.Q = @ConditionalGoldbach.normFunctional := rfl

theorem definition_046_weightEnergy : @TexAudit57.EnergyV = @ConditionalGoldbach.weightEnergy := rfl

theorem definition_047_functionalIntegrand : @TexAudit57.Psi = @ConditionalGoldbach.functionalIntegrand := rfl

theorem definition_048_strip : @TexAuditAB.variableStrip = @ConditionalGoldbach.strip := rfl

theorem definition_049_HardySpace : @TexAuditAB.variableHardySpace = @ConditionalGoldbach.HardySpace := rfl

theorem definition_050_boundaryPoint : @TexAuditAB.variableBoundary = @ConditionalGoldbach.boundaryPoint := rfl

theorem definition_051_residualOperator : @TexAuditAB.variableOperator = @ConditionalGoldbach.residualOperator := rfl

theorem definition_052_functionalValue : @TexAuditAB.variableFunctional = @ConditionalGoldbach.functionalValue := rfl

theorem definition_053_rieszVector : @TexAuditAB.variableVector = @ConditionalGoldbach.rieszVector := rfl

theorem definition_054_normFunctional : @TexAuditAB.variableFunctionalNorm = @ConditionalGoldbach.normFunctional := rfl

theorem definition_055_spectralComplex : @TexAuditAB.variableComplexProduct = @ConditionalGoldbach.spectralComplex := rfl

theorem definition_056_spectralQuaternion : @TexAuditAB.variableQuaternionProduct = @ConditionalGoldbach.spectralQuaternion := rfl

theorem definition_057_SpectralR : @TexAuditAB.pointwiseR = @ConditionalGoldbach.SpectralR := rfl

theorem definition_058_SpectralZeroFree : @TexAuditAB.pointwiseZeroFree = @ConditionalGoldbach.SpectralZeroFree := rfl

theorem definition_059_alpha : @TexAuditAB.boundaryParameter = @ConditionalGoldbach.alpha := rfl

theorem definition_060_HypothesisRAt : @TexAuditAB.eventualR = @ConditionalGoldbach.HypothesisRAt := rfl

theorem definition_061_HypothesisSAt : @TexAuditAB.eventualS = @ConditionalGoldbach.HypothesisSAt := rfl

theorem definition_062_zeroMultiplicity : @TexAuditAB.poleOrder = @ConditionalGoldbach.zeroMultiplicity := rfl

theorem definition_063_poleCoefficient : @TexAuditAB.poleMass = @ConditionalGoldbach.poleCoefficient := rfl

theorem definition_064_baselineProductR : @TexAuditAB.regularEulerFactor = @ConditionalGoldbach.baselineProductR := rfl

theorem definition_065_baselineBound : @TexAuditAB.operatorMajorant = @ConditionalGoldbach.baselineBound := rfl

theorem definition_066_balanceFactor : @TexAuditAB.boundaryCost = @ConditionalGoldbach.balanceFactor := rfl

theorem definition_067_experimentN : @TexAuditAB.numericalN = @ConditionalGoldbach.experimentN := rfl

theorem definition_068_cutoffPolynomial : @TexAuditAB.P = @ConditionalGoldbach.cutoffPolynomial := rfl

theorem definition_069_wideCutoff : @TexAuditAB.eta = @ConditionalGoldbach.wideCutoff := rfl

theorem definition_070_wideCompanion : @TexAuditAB.W = @ConditionalGoldbach.wideCompanion := rfl

theorem definition_071_wideWeight : @TexAuditAB.f = @ConditionalGoldbach.wideWeight := rfl

theorem definition_072_wideCorrelation : @TexAuditAB.J = @ConditionalGoldbach.wideCorrelation := rfl

theorem definition_073_unorderedPrimePairs : @TexAuditAB.primePairCount = @ConditionalGoldbach.unorderedPrimePairs := rfl

theorem definition_074_edgeCorrection : @TexAuditAB.edge = @ConditionalGoldbach.edgeCorrection := rfl

theorem definition_075_primePowerCorrection : @TexAuditAB.properPowers = @ConditionalGoldbach.primePowerCorrection := rfl

theorem definition_076_countingCoefficient : @TexAuditAB.coefficient = @ConditionalGoldbach.countingCoefficient := rfl

theorem definition_077_countingIntegral : @TexAuditAB.integralI = @ConditionalGoldbach.countingIntegral := rfl

theorem definition_078_diagonalCountingMoment : @TexAuditAB.diagonalD = @ConditionalGoldbach.diagonalCountingMoment := rfl

theorem definition_079_approxSignedMoment : @TexAuditAB.signedJhat = @ConditionalGoldbach.approxSignedMoment := rfl

theorem definition_080_approxDiagonalMoment : @TexAuditAB.diagonalDhat = @ConditionalGoldbach.approxDiagonalMoment := rfl

theorem definition_081_wideModelMass : @TexAuditAB.crossMass = @ConditionalGoldbach.wideModelMass := rfl

theorem definition_082_wideMainIntegral : @TexAuditAB.mainIntegral = @ConditionalGoldbach.wideMainIntegral := rfl

theorem definition_083_wideResidual : @TexAuditAB.residualB = @ConditionalGoldbach.wideResidual := rfl

theorem definition_084_HasMomentError : @TexAuditAB.momentError = @ConditionalGoldbach.HasMomentError := rfl

theorem definition_085_approxPrimeCount : @TexAuditAB.countCentre = @ConditionalGoldbach.approxPrimeCount := rfl

theorem definition_086_countError : @TexAuditAB.countRadius = @ConditionalGoldbach.countError := rfl

theorem definition_087_wideFunctional : @TexAuditAB.ellW = @ConditionalGoldbach.wideFunctional := rfl

theorem definition_088_wideRieszVector : @TexAuditAB.vectorW = @ConditionalGoldbach.wideRieszVector := rfl

theorem definition_089_spectralNode : @TexAuditAB.node = @ConditionalGoldbach.spectralNode := rfl

theorem definition_090_trapezoidWeight : @TexAuditAB.nodeWeight = @ConditionalGoldbach.trapezoidWeight := rfl

theorem definition_091_finiteSpectralMatrix : @TexAuditAB.matrixC = @ConditionalGoldbach.finiteSpectralMatrix := rfl

theorem definition_092_finiteSpectralFunction : @TexAuditAB.finiteX = @ConditionalGoldbach.finiteSpectralFunction := rfl

theorem definition_093_IsFiniteSpectrum : @TexAuditAB.finiteSpectrum = @ConditionalGoldbach.IsFiniteSpectrum := rfl

theorem definition_094_finiteEigenvalues : @TexAuditAB.eigenvalueList = @ConditionalGoldbach.finiteEigenvalues := rfl

theorem definition_095_finiteMatrixOpNorm : @TexAuditAB.matrixNorm = @ConditionalGoldbach.finiteMatrixOpNorm := rfl

end TexComparator
