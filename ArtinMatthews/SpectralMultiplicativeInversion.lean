module

public import ArtinMatthews.SpectralGamma0PoincareTrueWidthKL
public import Mathlib.Analysis.MellinTransform


set_option backward.privateInPublic true
@[expose] public section

/-! Exact inversion of the positive multiplicative Haar measure, with
integrability transported by the genuine Mellin change of variables. -/

noncomputable section
open Set MeasureTheory

namespace ArtinMatthews

theorem spectral_multiplicative_inverse_integral (F : ℝ → ℂ) {a : ℝ} (ha : 0 < a) :
    (∫ u in Ioi (0 : ℝ), F (a/u)/(u : ℂ)) = ∫ r in Ioi (0 : ℝ), F r/(r : ℂ) := by
  have h := mellin_comp_inv (fun u : ℝ => F (a*u)) (0 : ℂ)
  rw [neg_zero,mellin_comp_mul_left F 0 ha] at h
  simp only [neg_zero,Complex.cpow_zero,mellin,zero_sub,Complex.cpow_neg_one,smul_eq_mul,one_mul] at h
  convert h using 1
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro u _
    dsimp only
    simp only [div_eq_mul_inv]
    ring
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro r _
    dsimp only
    simp only [div_eq_mul_inv]
    ring

theorem spectral_multiplicative_inverse_integrable (F : ℝ → ℂ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun u : ℝ => F (a/u)/(u : ℂ)) (Ioi (0 : ℝ)) ↔
      IntegrableOn (fun r : ℝ => F r/(r : ℂ)) (Ioi (0 : ℝ)) := by
  have hi : MellinConvergent (fun u : ℝ => (fun r : ℝ => F (a*r)) (u^(-1 : ℝ))) 0 ↔
      MellinConvergent (fun r : ℝ => F (a*r)) 0 := by
    simpa only [zero_div] using
      (MellinConvergent.comp_rpow (f := fun r : ℝ => F (a*r)) (s := 0) (a := (-1 : ℝ)) (by norm_num))
  have h := hi.trans (MellinConvergent.comp_mul_left (f := F) (s := 0) ha)
  simp only [MellinConvergent,zero_sub,Complex.cpow_neg_one,smul_eq_mul,Real.rpow_neg_one] at h
  convert h using 1
  · exact integrableOn_congr_fun (fun u _ => by simp only [div_eq_mul_inv,mul_comm]) measurableSet_Ioi
  · exact integrableOn_congr_fun (fun r _ => by simp only [div_eq_mul_inv,mul_comm]) measurableSet_Ioi

end ArtinMatthews
