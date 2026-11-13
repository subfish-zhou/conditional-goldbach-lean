import ConditionalGoldbach.Proofs.VariableQuadratic
import ConditionalGoldbach.Proofs.ComponentNormBounds

set_option autoImplicit false
noncomputable section
open Set
namespace ConditionalGoldbach

lemma spectralScale_div_sqrt_width_eq (N : ℕ) (h : ℕ → ℝ)
    (hN : 0<(N:ℝ)) (hS : 0<singularSeries N) (hlog : 0<Real.log N)
    (hh : 0<h N) (hwidth : zeroFreeWidth N h<1) :
    spectralScale N/(2*Real.sqrt (zeroFreeWidth N h*(1-zeroFreeWidth N h)))=
      singularSeries N/(2*h N*Real.sqrt (1-zeroFreeWidth N h)) := by
  have hη : 0<zeroFreeWidth N h := by unfold zeroFreeWidth; positivity
  have hδ := spectralScale_pos N hN hS hlog
  have hid : (spectralScale N*h N)^2=singularSeries N^2*zeroFreeWidth N h := by
    rw [mul_pow,spectralScale_sq N hN hS.le hlog.le]
    unfold zeroFreeWidth
    field_simp
  have he : Real.sqrt (zeroFreeWidth N h)=spectralScale N*h N/singularSeries N := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt hη.le,div_pow]
    apply (eq_div_iff (pow_ne_zero 2 hS.ne')).mpr
    nlinarith [hid]
  rw [Real.sqrt_mul hη.le,he]
  have hs : Real.sqrt (1-zeroFreeWidth N h)≠0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  field_simp

lemma spectralZeroFree_of_log_square_bound (a : ℝ) (N : ℕ) [NeZero N]
    (ha0 : 0<a) (hN4 : 4≤N) (hGRH : GRH N) (ha : a<beta)
    (hlog : 1≤Real.log N) (hS : singularSeries N≤N)
    (C : ℝ) (hC : 1≤C) (hbound : ‖residualOperator ha N‖≤C*Real.log N^2) :
    SpectralZeroFree N a ha ((1/(16*C^2))*singularSeries N/(N*Real.log N)) := by
  let η : ℝ := (1/(16*C^2))*singularSeries N/(N*Real.log N)
  have hn : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hln : 0<Real.log N := by linarith
  have hSp := singularSeries_pos N
  have hCp : 0<C := by linarith
  have hη : 0<η := by dsimp [η]; positivity
  have hηsmall : η≤1/16 := by
    dsimp [η]
    apply (div_le_iff₀ (mul_pos hn hln)).mpr
    have h1 : 1/(16*C^2)≤1/16 := by
      apply (div_le_iff₀ (by positivity : 0<16*C^2)).mpr
      nlinarith
    have hh := mul_le_mul_of_nonneg_right h1 hSp.le
    nlinarith [mul_le_mul_of_nonneg_left hlog hn.le]
  have hδ := spectralScale_pos N hn hSp hln
  have hr : 0<Real.sqrt (η*(1-η)) := Real.sqrt_pos.mpr (mul_pos hη (by linarith))
  apply (variable_spectral_dictionary a ha0 N hN4 hGRH ha).2 η hη (by linarith) |>.mpr
  apply hbound.trans
  apply (le_div_iff₀ (by positivity : 0<2*Real.sqrt (η*(1-η)))).mpr
  apply (sq_le_sq₀ (by positivity) hδ.le).mp
  have hsqrt : Real.sqrt (η*(1-η))^2=η*(1-η) := Real.sq_sqrt (mul_pos hη (by linarith)).le
  have he : (C*Real.log N^2)^2*4*η=spectralScale N^2/4 := by
    rw [spectralScale_sq N hn hSp.le hln.le]
    dsimp [η]
    field_simp
    <;> ring
  calc
    _ = (C*Real.log N^2)^2*4*Real.sqrt (η*(1-η))^2 := by ring
    _ = ((C*Real.log N^2)^2*4*η)*(1-η) := by rw [hsqrt]; ring
    _ = (spectralScale N^2/4)*(1-η) := by rw [he]
    _ ≤ spectralScale N^2 := by nlinarith [sq_nonneg (spectralScale N)]

end ConditionalGoldbach
