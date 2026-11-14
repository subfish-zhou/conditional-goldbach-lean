module

public import ConditionalGoldbach.Proofs.HardyContinuousBoundary
public import ConditionalGoldbach.Proofs.HardyKernelPairing
public import ConditionalGoldbach.Proofs.SpectralL2BasisExistence

/-! Hardy kernel columns determine the entire range and the exact action of the boundary operator. -/
@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology ComplexConjugate
namespace ConditionalGoldbach

/-- Every column, including those indexed by boundary points, is a Hardy function with its
literal boundary restrictions as traces. -/
def HasHardyKernelColumns {a b : ℝ} (hab : a < b) (K : ℂ → ℂ → ℂ) : Prop :=
  ∀ s : ℂ, s.re ∈ Icc a b → ∃ g : HardySpace a b,
    (∀ z ∈ strip a b, fourierLaplace g z = K z s) ∧
    ((boundaryTraces hab g).1 =ᵐ[volume] fun t => K (line a t) s) ∧
    ((boundaryTraces hab g).2 =ᵐ[volume] fun t => K (line b t) s)

lemma hardyKernelColumns_of_majorant {a b : ℝ} (hab : a < b) (K : ℂ → ℂ → ℂ)
    (hhol : ∀ s : ℂ, s.re ∈ Icc a b → DifferentiableOn ℂ (fun z => K z s) (strip a b))
    (hc : ∀ s : ℂ, s.re ∈ Icc a b → ContinuousOn (fun z => K z s) {z : ℂ | z.re ∈ Icc a b})
    (hbound : ∀ s : ℂ, s.re ∈ Icc a b → ∃ M : ℝ → ℝ,
      Integrable M ∧ ∀ x ∈ Icc a b, ∀ t : ℝ, ‖K (line x t) s‖ ^ 2 ≤ M t) :
    HasHardyKernelColumns hab K := by
  intro s hs
  obtain ⟨M, hM, hbound⟩ := hbound s hs
  exact hardy_column_of_closedStrip_majorant hab (hhol s hs) (hc s hs) hM hbound

lemma hardyBoundary_inner_column {a b : ℝ} (hab : a < b) (K : ℂ → ℂ → ℂ)
    (hK : HermitianKernel K) (g : HardySpace a b) (s : ℂ)
    (hga : (boundaryTraces hab g).1 =ᵐ[volume] fun t => K (line a t) s)
    (hgb : (boundaryTraces hab g).2 =ᵐ[volume] fun t => K (line b t) s)
    (f : HardyBoundarySpace) :
    inner ℂ (hardyTraceIsometry hab g) f =
      (∫ t : ℝ, K s (line a t) * f.fst t) + ∫ t : ℝ, K s (line b t) * f.snd t := by
  change inner ℂ (WithLp.toLp 2 (boundaryTraces hab g)) f = _
  rw [WithLp.prod_inner_apply, L2.inner_def, L2.inner_def]
  congr 1
  · apply integral_congr_ae
    filter_upwards [hga] with t ht
    simp only [RCLike.inner_apply]
    rw [ht, ← hK s (line a t), mul_comm]
    rfl
  · apply integral_congr_ae
    filter_upwards [hgb] with t ht
    simp only [RCLike.inner_apply]
    rw [ht, ← hK s (line b t), mul_comm]
    rfl

lemma boundaryKernelOperator_kills_trace_orthogonal {a b : ℝ} (hab : a < b)
    (K : ℂ → ℂ → ℂ) (hherm : HermitianKernel K)
    (hK : ∀ x ∈ ({a, b} : Finset ℝ), ∀ y ∈ ({a, b} : Finset ℝ),
      MemLp (fun p : ℝ × ℝ => K (line x p.1) (line y p.2)) 2 volume)
    (hcol : HasHardyKernelColumns hab K)
    (f : HardyBoundarySpace)
    (hf : f ∈ (hardyTraceIsometry hab).toLinearMap.rangeᗮ) :
    boundaryKernelOperator a b K hK f = 0 := by
  have hp (x : ℝ) (hx : x ∈ Icc a b) (t : ℝ) :
      (∫ u : ℝ, K (line x t) (line a u) * f.fst u) +
        ∫ u : ℝ, K (line x t) (line b u) * f.snd u = 0 := by
    have hs : (line x t).re ∈ Icc a b := by simpa [line] using hx
    obtain ⟨g, _, hga, hgb⟩ := hcol (line x t) hs
    rw [← hardyBoundary_inner_column hab K hherm g (line x t) hga hgb f]
    exact (Submodule.mem_orthogonal _ _).mp hf _ ⟨g, rfl⟩
  obtain ⟨ha, hb⟩ := boundaryKernelOperator_coeFn a b K hK f
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [ha, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with t ht hz
    change (boundaryKernelOperator a b K hK f).fst t = _
    rw [ht, hp a ⟨le_rfl, hab.le⟩ t]
    exact hz.symm
  · apply Lp.ext
    filter_upwards [hb, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with t ht hz
    change (boundaryKernelOperator a b K hK f).snd t = _
    rw [ht, hp b ⟨hab.le, le_rfl⟩ t]
    exact hz.symm

lemma boundaryKernelOperator_range_hardy {a b : ℝ} (hab : a < b)
    (K : ℂ → ℂ → ℂ) (hherm : HermitianKernel K)
    (hK : ∀ x ∈ ({a, b} : Finset ℝ), ∀ y ∈ ({a, b} : Finset ℝ),
      MemLp (fun p : ℝ × ℝ => K (line x p.1) (line y p.2)) 2 volume)
    (hcol : HasHardyKernelColumns hab K) (f : HardyBoundarySpace) :
    boundaryKernelOperator a b K hK f ∈ Set.range (hardyTraceIsometry hab) := by
  let S := (hardyTraceIsometry hab).toLinearMap.range
  have hclosed : IsClosed (S : Set HardyBoundarySpace) := (hardyTraceIsometry hab).isometry.isClosedEmbedding.isClosed_range
  have he : Sᗮᗮ = S := by
    rw [Submodule.orthogonal_orthogonal_eq_closure, hclosed.submodule_topologicalClosure_eq]
  change boundaryKernelOperator a b K hK f ∈ S
  rw [← he, Submodule.mem_orthogonal]
  intro g hg
  have hs := (boundaryKernelOperator_isSelfAdjoint a b K hK
    (fun x _ y _ t u => hherm (line y u) (line x t))).isSymmetric
  calc
    inner ℂ g (boundaryKernelOperator a b K hK f) =
        inner ℂ (boundaryKernelOperator a b K hK g) f := (hs g f).symm
    _ = 0 := by rw [boundaryKernelOperator_kills_trace_orthogonal hab K hherm hK hcol g hg,
      inner_zero_left]

lemma boundaryKernelOperator_trace_evaluation {a b : ℝ} (hab : a < b)
    (K : ℂ → ℂ → ℂ) (hherm : HermitianKernel K)
    (hK : ∀ x ∈ ({a, b} : Finset ℝ), ∀ y ∈ ({a, b} : Finset ℝ),
      MemLp (fun p : ℝ × ℝ => K (line x p.1) (line y p.2)) 2 volume)
    (hcol : HasHardyKernelColumns hab K) (s : ℂ) (hs : s ∈ strip a b)
    (g : HardySpace a b)
    (hga : (boundaryTraces hab g).1 =ᵐ[volume] fun t => K (line a t) s)
    (hgb : (boundaryTraces hab g).2 =ᵐ[volume] fun t => K (line b t) s) :
    boundaryKernelOperator a b K hK (hardyTraceIsometry hab (evaluationVector s)) =
      hardyTraceIsometry hab g := by
  have hp (x : ℝ) (hx : x ∈ Icc a b) (t : ℝ) :
      (∫ u : ℝ, K (line x t) (line a u) * (boundaryTraces hab (evaluationVector s)).1 u) +
        ∫ u : ℝ, K (line x t) (line b u) * (boundaryTraces hab (evaluationVector s)).2 u =
          K (line x t) s := by
    have hz : (line x t).re ∈ Icc a b := by simpa [line] using hx
    obtain ⟨gz, hgz, hgza, hgzb⟩ := hcol (line x t) hz
    change (∫ u : ℝ, K (line x t) (line a u) *
        (hardyTraceIsometry hab (evaluationVector s)).fst u) +
      ∫ u : ℝ, K (line x t) (line b u) *
        (hardyTraceIsometry hab (evaluationVector s)).snd u = _
    rw [← hardyBoundary_inner_column hab K hherm gz (line x t) hgza hgzb,
      (hardyTraceIsometry hab).inner_map_map]
    calc
      inner ℂ gz (evaluationVector s) = conj (inner ℂ (evaluationVector s) gz) :=
        (inner_conj_symm _ _).symm
      _ = conj (fourierLaplace gz s) := by rw [evaluationVector_spec hs]; rfl
      _ = K (line x t) s := by rw [hgz s hs, ← hherm (line x t) s]
  obtain ⟨ha, hb⟩ := boundaryKernelOperator_coeFn a b K hK
    (hardyTraceIsometry hab (evaluationVector s))
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [ha, hga] with t ht hg
    change (boundaryKernelOperator a b K hK (hardyTraceIsometry hab (evaluationVector s))).fst t = _
    rw [ht]
    exact (hp a ⟨le_rfl, hab.le⟩ t).trans hg.symm
  · apply Lp.ext
    filter_upwards [hb, hgb] with t ht hg
    change (boundaryKernelOperator a b K hK (hardyTraceIsometry hab (evaluationVector s))).snd t = _
    rw [ht]
    exact (hp b ⟨hab.le, le_rfl⟩ t).trans hg.symm

lemma hardyBoundaryCompression_represents {a : ℝ} (ha : a < beta) (N : ℕ) [NeZero N]
    (K : ℂ → ℂ → ℂ) (hherm : HermitianKernel K)
    (hK : ∀ x ∈ ({a, beta} : Finset ℝ), ∀ y ∈ ({a, beta} : Finset ℝ),
      MemLp (fun p : ℝ × ℝ => K (line x p.1) (line y p.2)) 2 volume)
    (hcol : HasHardyKernelColumns ha K) :
    RepresentsKernel ha N K (hardyBoundaryCompression ha (boundaryKernelOperator a beta K hK)) := by
  intro f s hs
  obtain ⟨g, hg, hga, hgb⟩ := hcol s ⟨hs.1.le, hs.2.le⟩
  rw [evaluationVector_spec hs]
  change inner ℂ (evaluationVector s)
    (hardyBoundaryCompression ha (boundaryKernelOperator a beta K hK) f) = _
  rw [hardyBoundaryCompression_inner]
  have hself := (boundaryKernelOperator_isSelfAdjoint a beta K hK
    (fun x _ y _ t u => hherm (line y u) (line x t))).isSymmetric
  calc
    inner ℂ (hardyTraceIsometry ha (evaluationVector s))
        (boundaryKernelOperator a beta K hK (hardyTraceIsometry ha f)) =
      inner ℂ (boundaryKernelOperator a beta K hK (hardyTraceIsometry ha (evaluationVector s)))
        (hardyTraceIsometry ha f) := (hself _ _).symm
    _ = inner ℂ (hardyTraceIsometry ha g) (hardyTraceIsometry ha f) := by
      rw [boundaryKernelOperator_trace_evaluation ha K hherm hK hcol s hs g hga hgb]
    _ = kernelAction ha N K f s := hardyBoundary_inner_column ha K hherm g s hga hgb _

lemma kernelOperator_eq_boundaryCompression {a : ℝ} (ha : a < beta) (N : ℕ) [NeZero N]
    (K : ℂ → ℂ → ℂ) (hherm : HermitianKernel K)
    (hK : ∀ x ∈ ({a, beta} : Finset ℝ), ∀ y ∈ ({a, beta} : Finset ℝ),
      MemLp (fun p : ℝ × ℝ => K (line x p.1) (line y p.2)) 2 volume)
    (hcol : HasHardyKernelColumns ha K) :
    kernelOperator ha N K = hardyBoundaryCompression ha (boundaryKernelOperator a beta K hK) :=
  kernelOperator_eq_of_represents ha N (hardyBoundaryCompression_represents ha N K hherm hK hcol)

lemma kernelOperator_pairing_of_hardyColumns {a : ℝ} (ha : a < beta) (N : ℕ) [NeZero N]
    (K : ℂ → ℂ → ℂ) (hherm : HermitianKernel K)
    (hK : ∀ x ∈ ({a, beta} : Finset ℝ), ∀ y ∈ ({a, beta} : Finset ℝ),
      MemLp (fun p : ℝ × ℝ => K (line x p.1) (line y p.2)) 2 volume)
    (hcol : HasHardyKernelColumns ha K) (s z : ℂ)
    (hs : s ∈ strip a beta) (hz : z ∈ strip a beta) :
    K s z = paperInner (kernelOperator ha N K (evaluationVector z)) (evaluationVector s) := by
  apply kernelOperator_pairing_of_columns ha N K hherm
    ⟨_, hardyBoundaryCompression_represents ha N K hherm hK hcol⟩
    (fun w hw => hcol w ⟨hw.1.le, hw.2.le⟩) s z hs hz

lemma kernelAction_integrable_of_hardyColumns {a : ℝ} (ha : a < beta)
    (K : ℂ → ℂ → ℂ) (hherm : HermitianKernel K) (hcol : HasHardyKernelColumns ha K)
    (h : HardySpace a beta) (s : ℂ) (hs : s ∈ strip a beta) :
    Integrable (fun t : ℝ => K s (line a t) * (boundaryTraces ha h).1 t) ∧
    Integrable (fun t : ℝ => K s (line beta t) * (boundaryTraces ha h).2 t) := by
  obtain ⟨g, _, hga, hgb⟩ := hcol s ⟨hs.1.le, hs.2.le⟩
  constructor
  · apply (L2.integrable_inner (𝕜 := ℂ) (boundaryTraces ha g).1 (boundaryTraces ha h).1).congr
    filter_upwards [hga] with t ht
    simp only [RCLike.inner_apply, ht]
    rw [← hherm s (line a t), mul_comm]
  · apply (L2.integrable_inner (𝕜 := ℂ) (boundaryTraces ha g).2 (boundaryTraces ha h).2).congr
    filter_upwards [hgb] with t ht
    simp only [RCLike.inner_apply, ht]
    rw [← hherm s (line beta t), mul_comm]

lemma kernelOperator_spec_of_hardyColumns {a : ℝ} (ha : a < beta) (N : ℕ) [NeZero N]
    (K : ℂ → ℂ → ℂ) (hherm : HermitianKernel K)
    (hK : ∀ x ∈ ({a, beta} : Finset ℝ), ∀ y ∈ ({a, beta} : Finset ℝ),
      MemLp (fun p : ℝ × ℝ => K (line x p.1) (line y p.2)) 2 volume)
    (hcol : HasHardyKernelColumns ha K) :
    let T := kernelOperator ha N K
    RepresentsKernel ha N K T ∧ IsCompactOperator T ∧ IsSelfAdjoint T ∧
      IsHilbertSchmidt T ∧ Nonempty (SpectralData T) ∧
      (∑' j, eigenvalues T j ^ 2) = hsNorm T ^ 2 ∧
      hsNorm T ^ 2 = BoundaryKernelSquareIntegral a beta K ∧
      ‖T‖ = sSup (Set.range (fun j => |eigenvalues T j|)) ∧
      (T ≠ 0 → ∃ j, |eigenvalues T j| = ‖T‖) := by
  dsimp only
  rw [kernelOperator_eq_boundaryCompression ha N K hherm hK hcol]
  exact ⟨hardyBoundaryCompression_represents ha N K hherm hK hcol,
    hardyBoundaryKernel_spectral_spec_no_basis ha K hK
      (fun x _ y _ t u => hherm (line y u) (line x t))
      (boundaryKernelOperator_range_hardy ha K hherm hK hcol)⟩

end ConditionalGoldbach
