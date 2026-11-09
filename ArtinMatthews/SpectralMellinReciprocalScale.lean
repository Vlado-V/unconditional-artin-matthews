module

public import Mathlib.Analysis.MellinTransform


set_option backward.privateInPublic true
@[expose] public section

/-! Exact Mellin transport for a power times a reciprocal dilation. -/

noncomputable section
open Set MeasureTheory

namespace ArtinMatthews

theorem spectral_mellin_cpow_comp_div (f : ℝ → ℂ) {b : ℝ} (hb : 0 < b) (a s : ℂ) :
    mellin (fun x : ℝ => (x : ℂ)^a*f (b/x)) s =
      (b : ℂ)^(s+a)*mellin f (-(s+a)) := by
  change mellin (fun x : ℝ => (x : ℂ)^a • f (b/x)) s = _
  rw [mellin_cpow_smul]
  have he : (fun x : ℝ => f (b/x)) = (fun x : ℝ => (fun y : ℝ => f (b*y)) x⁻¹) := by
    funext x
    simp only [div_eq_mul_inv]
  rw [he,mellin_comp_inv (fun y : ℝ => f (b*y)) (s+a),
    mellin_comp_mul_left f (-(s+a)) hb,neg_neg,smul_eq_mul]

theorem spectral_mellinConvergent_cpow_comp_div (f : ℝ → ℂ) {b : ℝ} (hb : 0 < b) (a s : ℂ) :
    MellinConvergent (fun x : ℝ => (x : ℂ)^a*f (b/x)) s ↔
      MellinConvergent f (-(s+a)) := by
  change MellinConvergent (fun x : ℝ => (x : ℂ)^a • f (b/x)) s ↔ _
  rw [MellinConvergent.cpow_smul]
  have h := MellinConvergent.comp_rpow
    (f := fun y : ℝ => f (b*y)) (s := s+a) (a := -1) (by norm_num)
  have he : (fun x : ℝ => f (b/x)) = (fun x : ℝ => f (b*(x^(-1 : ℝ)))) := by
    funext x
    simp only [Real.rpow_neg_one,div_eq_mul_inv]
  rw [he]
  have h' : MellinConvergent (fun x : ℝ => f (b*(x^(-1 : ℝ)))) (s+a) ↔
      MellinConvergent (fun y : ℝ => f (b*y)) (-(s+a)) := by
    simpa only [Complex.ofReal_neg,Complex.ofReal_one,div_neg,div_one] using h
  exact h'.trans (MellinConvergent.comp_mul_left hb)

end ArtinMatthews
