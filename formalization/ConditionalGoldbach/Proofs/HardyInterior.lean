import ConditionalGoldbach.Proofs.HardyFourier
import ConditionalGoldbach.Proofs.HardyWeights

/-! The Fourier–Laplace transform has an L² restriction to every interior vertical line. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Filter Set Complex FourierTransform
namespace ConditionalGoldbach

lemma fourierLaplace_line_eq_classical_fourier {a b : ℝ} (ψ : HardySpace a b) (x t : ℝ) :
    fourierLaplace ψ (line x t) = (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ *
      𝓕 (fun τ : ℝ => (Real.exp (x * τ) : ℂ) * ψ τ) (-t / (2 * Real.pi)) := by
  unfold fourierLaplace
  congr 1
  rw [Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards [] with τ
  have phase : -2 * Real.pi * inner ℝ τ (-t / (2 * Real.pi)) = τ * t := by
    simp only [real_inner_comm, Real.inner_apply]
    field_simp
  rw [phase, smul_eq_mul, Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  rw [mul_comm (ψ τ)]
  congr 1
  congr 1
  simp only [line, Complex.ofReal_mul, Complex.ofReal_add]
  ring

lemma hardy_interiorLine_memLp {a b x : ℝ} (hab : a < b)
    (hx : x ∈ Ioo a b) (ψ : HardySpace a b) :
    MemLp (fun t : ℝ => fourierLaplace ψ (line x t)) 2 volume := by
  have hf := classical_fourier_memLp (hardy_weighted_line_integrable hx ψ)
    (hardy_weighted_line_memLp ⟨hx.1.le, hx.2.le⟩ ψ)
  have hs := memLp_comp_real_mul hf (c := -(2 * Real.pi)⁻¹)
    (neg_ne_zero.mpr (inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)))
  have hm := hs.const_mul ((Real.sqrt (2 * Real.pi) : ℂ)⁻¹)
  convert hm using 1
  funext t
  rw [fourierLaplace_line_eq_classical_fourier]
  congr 2
  ring

end ConditionalGoldbach
