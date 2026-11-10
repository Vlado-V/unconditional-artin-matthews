module

public import ArtinMatthews.SpectralHyperbolicBochnerCoordinates
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Group.Prod
import ArtinMatthews.SpectralHyperbolicGreen


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine weak derivative pairings for the invariant H² measure. The test
coefficients are chosen so that the density cancels: y²Dφ pairs with the
value and yφ pairs with the actual orthonormal-frame derivative yDF. -/

noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace ArtinMatthews

local instance : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
  change (volume.prod volume : Measure (ℝ × ℝ)).IsAddHaarMeasure
  infer_instance

/-- Euclidean integration by parts with a genuine compact smooth test;
no compact support is imposed on the differentiated source. -/
theorem spectral_plane_weak_pairing (F φ : ℝ × ℝ → ℂ)
    (hF : ContDiff ℝ ∞ F) (hφ : ContDiff ℝ ∞ φ)
    (hs : HasCompactSupport φ) (v : ℝ × ℝ) :
    (∫ p, F p * fderiv ℝ φ p v) = -∫ p, fderiv ℝ F p v * φ p := by
  have hDF : Continuous (fun p => fderiv ℝ F p v) :=
    (hF.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDφ : Continuous (fun p => fderiv ℝ φ p v) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hsD : HasCompactSupport (fun p => fderiv ℝ φ p v) := hs.fderiv_apply ℝ v
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    ((hDF.mul hφ.continuous).integrable_of_hasCompactSupport hs.mul_left)
    ((hF.continuous.mul hDφ).integrable_of_hasCompactSupport hsD.mul_left)
    ((hF.continuous.mul hφ.continuous).integrable_of_hasCompactSupport hs.mul_left)
    (fun p _ => hF.differentiable (by simp) p)
    (fun p _ => hφ.differentiable (by simp) p)

/-- Actual H² weak pairing in every real coordinate direction. Both sides
are literal integrals against Mathlib's invariant hyperbolic volume. -/
theorem h2_plane_weak_pairing (F φ : ℝ × ℝ → ℂ)
    (hF : ContDiff ℝ ∞ F) (hφ : ContDiff ℝ ∞ φ)
    (hs : HasCompactSupport φ)
    (hpositive : tsupport φ ⊆ {p : ℝ × ℝ | 0 < p.2}) (v : ℝ × ℝ) :
    (∫ z : UpperHalfPlane, (z.im^2 : ℝ) •
      (F (z.re,z.im) * fderiv ℝ φ (z.re,z.im) v)) =
      -∫ z : UpperHalfPlane, (z.im • fderiv ℝ F (z.re,z.im) v) *
        (z.im • φ (z.re,z.im)) := by
  have hzero {p : ℝ × ℝ} (hp : ¬ 0 < p.2) : φ p = 0 :=
    image_eq_zero_of_notMem_tsupport (fun ht => hp (hpositive ht))
  have hDzero {p : ℝ × ℝ} (hp : ¬ 0 < p.2) : fderiv ℝ φ p v = 0 :=
    image_eq_zero_of_notMem_tsupport (f := fun q => fderiv ℝ φ q v)
      (fun ht => hp (hpositive (tsupport_fderiv_apply_subset ℝ v ht)))
  have hleft := upperHalfPlane_integral_height_sq
    (fun p => F p * fderiv ℝ φ p v) (fun p hp => by rw [hDzero hp,mul_zero])
  have hright := upperHalfPlane_integral_height_sq
    (fun p => fderiv ℝ F p v * φ p) (fun p hp => by rw [hzero hp,mul_zero])
  have he (z : UpperHalfPlane) :
      (z.im • fderiv ℝ F (z.re,z.im) v) * (z.im • φ (z.re,z.im)) =
        (z.im^2 : ℝ) • (fderiv ℝ F (z.re,z.im) v * φ (z.re,z.im)) := by
    simp only [Complex.real_smul, Complex.ofReal_pow]
    ring
  simp_rw [he]
  rw [hleft,hright]
  exact spectral_plane_weak_pairing F φ hF hφ hs v

end ArtinMatthews
