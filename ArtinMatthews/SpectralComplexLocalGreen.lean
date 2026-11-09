module

public import ArtinMatthews.SpectralHyperbolicWeakPairing
public import Mathlib.Analysis.Calculus.FDeriv.Star


set_option backward.privateInPublic true
@[expose] public section

/-! Complex Green identity for actual compact smooth plane tests against a
smooth source; all derivative pairings are proved integrable by compact test
support. This is the local differential input to the represented H² form. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff InnerProductSpace

namespace ArtinMatthews

theorem spectral_plane_complex_green_direction (φ F : ℝ × ℝ → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hF : ContDiff ℝ ∞ F)
    (hs : HasCompactSupport φ) (v : ℝ × ℝ) :
    (∫ p, inner ℂ (fderiv ℝ φ p v) (fderiv ℝ F p v)) =
      ∫ p, inner ℂ (-fderiv ℝ (fun q => fderiv ℝ φ q v) p v) (F p) := by
  have hd : ContDiff ℝ ∞ (fun p => fderiv ℝ φ p v) :=
    (hφ.fderiv_right (by simp)).clm_apply contDiff_const
  have hstar : ContDiff ℝ ∞ (fun p => star (fderiv ℝ φ p v)) :=
    (starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp hd
  have hc : HasCompactSupport (fun p => star (fderiv ℝ φ p v)) :=
    (hs.fderiv_apply ℝ v).comp_left (by simp)
  have h := spectral_plane_weak_pairing F (fun p => star (fderiv ℝ φ p v)) hF hstar hc v
  have he (p : ℝ × ℝ) :
      fderiv ℝ (fun q => star (fderiv ℝ φ q v)) p v =
        star (fderiv ℝ (fun q => fderiv ℝ φ q v) p v) := by
    rw [fderiv_star,ContinuousLinearMap.comp_apply]
    rfl
  simp_rw [he] at h
  simp only [RCLike.inner_apply,starRingEnd_apply,
    star_neg,mul_neg,integral_neg]
  exact neg_eq_iff_eq_neg.mp h.symm

end ArtinMatthews
