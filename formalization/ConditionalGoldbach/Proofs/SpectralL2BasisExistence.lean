module

public import ConditionalGoldbach.Proofs.SpectralHardyCompression
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Filter Set Complex InnerProductSpace
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable

/-- A separable Hilbert space containing infinitely many independent vectors has a natural-indexed basis. -/
theorem exists_nat_hilbertBasis_of_linearIndependent {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [SecondCountableTopology H]
    (v : ℕ → H) (hv : LinearIndependent ℂ v) : Nonempty (HilbertBasis ℕ ℂ H) := by
  obtain ⟨w, b, hb⟩ := exists_hilbertBasis ℂ H
  have : DiscreteTopology w := DiscreteTopology.of_forall_le_dist (r := 1) zero_lt_one (by
    intro x y hxy
    have hn := norm_sub_sq (𝕜 := ℂ) (b x) (b y)
    rw [b.orthonormal.norm_eq_one, b.orthonormal.norm_eq_one,
      b.orthonormal.inner_eq_zero hxy] at hn
    have hd : dist x y = ‖b x - b y‖ := by rw [hb, Subtype.dist_eq, dist_eq_norm]
    rw [hd]
    simp only [map_zero, mul_zero, sub_zero, one_pow] at hn
    nlinarith [norm_nonneg (b x - b y)])
  have : Countable w := countable_of_Lindelof_of_discrete
  have : Infinite w := by
    by_contra h
    have : Finite w := not_infinite_iff_finite.mp h
    let : Fintype w := Fintype.ofFinite w
    have : Module.Finite ℂ H := Module.Finite.of_basis b.toOrthonormalBasis.toBasis
    have : Finite ℕ := hv.finite
    exact _root_.not_finite ℕ
  exact ⟨hilbertBasisReindex b (Classical.choice inferInstance : ℕ ≃ w)⟩

/-- Unit intervals provide infinitely many independent vectors in any locally finite measure equivalent to Lebesgue measure. -/
theorem real_l2_exists_nat_hilbertBasis (μ : Measure ℝ) [IsLocallyFiniteMeasure μ]
    (hμ : (volume : Measure ℝ) ≪ μ) : Nonempty (HilbertBasis ℕ ℂ (Lp ℂ 2 μ)) := by
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  let v : ℕ → Lp ℂ 2 μ := fun n => indicatorConstLp 2
    (s := Ioc (n : ℝ) (n + 1)) measurableSet_Ioc measure_Ioc_lt_top.ne (1 : ℂ)
  have hv0 (n : ℕ) : v n ≠ 0 := by
    have hm : μ (Ioc (n : ℝ) (n + 1)) ≠ 0 := by
      intro hz
      have hz' := hμ hz
      rw [Real.volume_Ioc] at hz'
      norm_num at hz'
    have hp : 0 < ‖v n‖ := by
      dsimp only [v]
      rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
      exact mul_pos (by norm_num) (Real.rpow_pos_of_pos
        (ENNReal.toReal_pos hm measure_Ioc_lt_top.ne) _)
    exact norm_ne_zero_iff.mp hp.ne'
  have horth : Pairwise (fun i j => inner ℂ (v i) (v j) = 0) := by
    intro i j hij
    rw [L2.inner_def]
    apply integral_eq_zero_of_ae
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Ioc)
        (hμs := measure_Ioc_lt_top.ne) (c := (1 : ℂ)) (μ := μ)
        (s := Ioc (i : ℝ) (i + 1)),
      indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Ioc)
        (hμs := measure_Ioc_lt_top.ne) (c := (1 : ℂ)) (μ := μ)
        (s := Ioc (j : ℝ) (j + 1))] with t hi hj
    change inner ℂ (v i t) (v j t) = 0
    change (indicatorConstLp 2 measurableSet_Ioc measure_Ioc_lt_top.ne (1 : ℂ)) t = _ at hi
    change (indicatorConstLp 2 measurableSet_Ioc measure_Ioc_lt_top.ne (1 : ℂ)) t = _ at hj
    dsimp only [v]
    rw [hi, hj]
    change inner ℂ ((Ioc (i : ℝ) (i + 1)).indicator (fun _ => (1 : ℂ)) t)
      ((Ioc (j : ℝ) (j + 1)).indicator (fun _ => (1 : ℂ)) t) = 0
    · by_cases hti : t ∈ Ioc (i : ℝ) (i + 1)
      · have htj : t ∉ Ioc (j : ℝ) (j + 1) := by
          intro htj
          rcases lt_or_gt_of_ne hij with hij | hji
          · have hle : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
            linarith [hti.2, htj.1]
          · have hle : (j : ℝ) + 1 ≤ i := by exact_mod_cast hji
            linarith [htj.2, hti.1]
        simp [Set.indicator_of_notMem htj]
      · simp [Set.indicator_of_notMem hti]
  exact exists_nat_hilbertBasis_of_linearIndependent v
    (linearIndependent_of_ne_zero_of_inner_eq_zero hv0 horth)

/-- The unweighted boundary space admits the indexing convention used throughout the paper. -/
theorem boundaryL2_exists_nat_hilbertBasis : Nonempty (HilbertBasis ℕ ℂ BoundaryL2) :=
  real_l2_exists_nat_hilbertBasis volume Measure.AbsolutelyContinuous.rfl

/-- The Fourier-density model of the Hardy space has a countable infinite Hilbert basis. -/
theorem hardySpace_exists_nat_hilbertBasis (a b : ℝ) :
    Nonempty (HilbertBasis ℕ ℂ (HardySpace a b)) := by
  have : IsLocallyFiniteMeasure (hardyMeasure a b) :=
    IsLocallyFiniteMeasure.withDensity_ofReal (hardyWeight_continuous a b)
  exact real_l2_exists_nat_hilbertBasis _ (volume_absolutelyContinuous_hardyMeasure a b)

/-- The full spectral package for a supported Hardy boundary kernel, with no basis assumptions. -/
theorem hardyBoundaryKernel_spectral_spec_no_basis {a : ℝ} (ha : a < beta) (K : ℂ → ℂ → ℂ)
    (hK : ∀ x ∈ ({a, beta} : Finset ℝ), ∀ y ∈ ({a, beta} : Finset ℝ),
      MemLp (fun p : ℝ × ℝ => K (line x p.1) (line y p.2)) 2 volume)
    (hherm : ∀ x ∈ ({a, beta} : Finset ℝ), ∀ y ∈ ({a, beta} : Finset ℝ), ∀ t u : ℝ,
      K (line y u) (line x t) = conj (K (line x t) (line y u)))
    (hR : ∀ f, boundaryKernelOperator a beta K hK f ∈ Set.range (hardyTraceIsometry ha)) :
    let T := hardyBoundaryCompression ha (boundaryKernelOperator a beta K hK)
    IsCompactOperator T ∧ IsSelfAdjoint T ∧ IsHilbertSchmidt T ∧ Nonempty (SpectralData T) ∧
      (∑' j, eigenvalues T j ^ 2) = hsNorm T ^ 2 ∧
      hsNorm T ^ 2 = BoundaryKernelSquareIntegral a beta K ∧
      ‖T‖ = sSup (Set.range (fun j => |eigenvalues T j|)) ∧
      (T ≠ 0 → ∃ j, |eigenvalues T j| = ‖T‖) :=
  hardyBoundaryKernel_spectral_spec ha K hK hherm hR
    (Classical.choice boundaryL2_exists_nat_hilbertBasis)
    (Classical.choice (hardySpace_exists_nat_hilbertBasis a beta))

end ConditionalGoldbach
