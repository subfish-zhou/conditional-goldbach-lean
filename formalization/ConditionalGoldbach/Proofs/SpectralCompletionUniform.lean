module

public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
public import ConditionalGoldbach.Proofs.SpectralCompletion

public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Filter Set Complex
namespace ConditionalGoldbach
attribute [local instance] Classical.propDecidable
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- All complex slices have the same norm. -/
theorem quaternion_algHom_norm (f : ℂ →ₐ[ℝ] Quaternion ℝ) (z : ℂ) : ‖f z‖ = ‖z‖ := by
  have heq : Quaternion.normSq (f z) = Complex.normSq z := by
    apply Quaternion.coe_inj.mp
    rw [← Quaternion.self_mul_star, ← quaternion_algHom_map_conj, ← map_mul,
      Complex.mul_conj]
    exact f.commutes _
  rw [Quaternion.normSq_eq_norm_mul_self, Complex.normSq_eq_norm_sq] at heq
  nlinarith [norm_nonneg (f z), norm_nonneg z]

/-- Uniform convergence of the complex spectral products on each compact set. -/
theorem spectralComplex_hasProdUniformlyOn (N : ℕ) (T : H →L[ℂ] H)
    (hT : Nonempty (SpectralData T)) (K : Set ℂ) (hK : IsCompact K) :
    HasProdUniformlyOn (fun j (q : ℂ) =>
      (1 - (4 * eigenvalues T j ^ 2 / spectralScale N ^ 2 : ℝ) * q * (1 - q)))
      (spectralComplex N T) K := by
  obtain ⟨B, hB, hKB⟩ := hK.isBounded.subset_closedBall_lt 0 0
  have hbound (q : ℂ) (hq : q ∈ K) : ‖q‖ ≤ B := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hKB hq
  let c : ℕ → ℝ := fun j => 4 * eigenvalues T j ^ 2 / spectralScale N ^ 2
  have hc (j : ℕ) : 0 ≤ c j := by dsimp [c]; positivity
  have hs : Summable (fun j => c j * B * (1 + B)) := by
    convert (((eigenvalues_square_summable T hT).mul_left (4 / spectralScale N ^ 2)).mul_right B).mul_right (1 + B) using 1
    funext j
    dsimp [c]
    ring
  have hu := hs.hasProdUniformlyOn_nat_one_add hK
    (f := fun j (q : ℂ) => -((c j : ℂ) * q * (1 - q)))
    (by
      filter_upwards with j q hq
      simp only [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc j)]
      apply mul_le_mul (mul_le_mul_of_nonneg_left (hbound q hq) (hc j))
        ((norm_sub_le 1 q).trans (by simpa using add_le_add_left (hbound q hq) 1))
        (norm_nonneg _) (mul_nonneg (hc j) hB.le))
    (by intro j; fun_prop)
  convert hu using 1; ext; simp only [c, spectralComplex, sub_eq_add_neg]

theorem spectralComplex_tendstoUniformlyOn (N : ℕ) (T : H →L[ℂ] H)
    (hT : Nonempty (SpectralData T)) (K : Set ℂ) (hK : IsCompact K) :
    TendstoUniformlyOn (fun k (q : ℂ) => ∏ j ∈ Finset.range k,
      (1 - (4 * eigenvalues T j ^ 2 / spectralScale N ^ 2 : ℝ) * q * (1 - q)))
      (spectralComplex N T) atTop K :=
  (spectralComplex_hasProdUniformlyOn N T hT K hK).tendstoUniformlyOn_finsetRange

/-- The scalar product is an entire function. -/
theorem spectralComplex_differentiable (N : ℕ) (T : H →L[ℂ] H)
    (hT : Nonempty (SpectralData T)) : Differentiable ℂ (spectralComplex N T) := by
  have hlocal : TendstoLocallyUniformlyOn (fun k (q : ℂ) => ∏ j ∈ Finset.range k,
      (1 - (4 * eigenvalues T j ^ 2 / spectralScale N ^ 2 : ℝ) * q * (1 - q)))
      (spectralComplex N T) atTop univ := by
    apply (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).2
    intro K _ hK
    exact spectralComplex_tendstoUniformlyOn N T hT K hK
  have hd := hlocal.differentiableOn (by
    filter_upwards with k
    apply Differentiable.differentiableOn
    fun_prop) isOpen_univ
  exact differentiableOn_univ.mp hd

/-- The quaternionic product inherits uniform convergence through norm-preserving complex slices. -/
theorem spectralQuaternion_compactUniformLimit (N : ℕ) (T : H →L[ℂ] H)
    (hT : Nonempty (SpectralData T)) :
    CompactUniformLimit (fun k q => spectralPartialQuaternion N T q k) (spectralQuaternion N T) := by
  intro K hK ε hε
  obtain ⟨B, _, hKB⟩ := hK.isBounded.subset_closedBall_lt 0 0
  have hu := spectralComplex_tendstoUniformlyOn N T hT
    (Metric.closedBall 0 B) (isCompact_closedBall 0 B)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 ((Metric.tendstoUniformlyOn_iff.1 hu) ε hε)
  refine ⟨n₀, fun n hn q hq => ?_⟩
  obtain ⟨f, z, rfl⟩ := quaternion_exists_complex_slice q
  have hz : z ∈ Metric.closedBall 0 B := by
    have := hKB hq
    simpa only [Metric.mem_closedBall, dist_zero_right, quaternion_algHom_norm] using this
  have hh := hn₀ n hn z hz
  dsimp only
  rw [spectralPartialQuaternion_map, spectralQuaternion_apply_algHom N T hT,
    ← map_sub, quaternion_algHom_norm]
  simpa only [dist_eq_norm, norm_sub_rev] using hh

/-- The quaternionic extension is intrinsic and entire on every complex slice. -/
theorem spectralQuaternion_intrinsicEntire (N : ℕ) (T : H →L[ℂ] H)
    (hT : Nonempty (SpectralData T)) : IntrinsicEntire (spectralQuaternion N T) := by
  refine ⟨spectralComplex N T, spectralComplex_differentiable N T hT,
    spectralComplex_conj N T hT, ?_⟩
  intro J _ hJsq z
  exact spectralQuaternion_apply_algHom N T hT
    (Complex.liftAux J (by simpa only [pow_two] using hJsq)) z

end ConditionalGoldbach
