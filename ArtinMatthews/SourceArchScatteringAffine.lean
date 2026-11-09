module

public import ArtinMatthews.SourceArchSelfDualMeasure
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace


set_option backward.privateInPublic true
@[expose] public section

/-! Translation and real dilation for the actual complex trace measure. -/
namespace ArtinMatthews.SourceArchJacquet

open MeasureTheory
open ArtinMatthews.VaryingKummerAnalytic
noncomputable section

theorem sourceArchTraceIntegral_affine (f : ℂ → ℂ) (u : ℂ) {H : ℝ} (hH : 0 < H) :
    (∫ x : ℂ, f ((x + u) / (H : ℂ)) ∂sourceComplexTraceMeasure) =
      (H ^ 2 : ℝ) * ∫ x : ℂ, f x ∂sourceComplexTraceMeasure := by
  have : sourceComplexTraceMeasure.IsAddHaarMeasure := by
    exact Measure.IsAddHaarMeasure.smul volume (by norm_num : (2 : ENNReal) ≠ 0)
      (by norm_num : (2 : ENNReal) ≠ ⊤)
  have he : (fun x : ℂ => f ((x + u) / (H : ℂ))) =
      (fun x : ℂ => f ((H⁻¹ : ℝ) • (x + u))) := by
    funext x
    congr 1
    rw [Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
    ring
  rw [he, integral_add_right_eq_self (fun x : ℂ => f ((H⁻¹ : ℝ) • x)) u,
    Measure.integral_comp_smul sourceComplexTraceMeasure f H⁻¹]
  simp [Complex.finrank_real_complex, inv_pow, abs_of_nonneg (sq_pos_of_pos hH).le]

theorem sourceArchTraceIntegrable_affine (f : ℂ → ℂ) (u : ℂ) {H : ℝ} (hH : 0 < H)
    (hf : Integrable f sourceComplexTraceMeasure) :
    Integrable (fun x : ℂ => f ((x + u) / (H : ℂ))) sourceComplexTraceMeasure := by
  have : sourceComplexTraceMeasure.IsAddHaarMeasure := by
    exact Measure.IsAddHaarMeasure.smul volume (by norm_num : (2 : ENNReal) ≠ 0)
      (by norm_num : (2 : ENNReal) ≠ ⊤)
  have h := (hf.comp_smul (inv_ne_zero hH.ne')).comp_add_right u
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  congr 1
  rw [Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
  ring

end
end ArtinMatthews.SourceArchJacquet
