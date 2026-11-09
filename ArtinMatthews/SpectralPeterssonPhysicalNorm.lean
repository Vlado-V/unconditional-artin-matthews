module

public import ArtinMatthews.SpectralPeterssonWeightedNorm


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine Petersson self-pair is the real physical weighted norm. -/
noncomputable section
open UpperHalfPlane MeasureTheory
open scoped ComplexConjugate

namespace ArtinMatthews

theorem spectralPetersson_self_pair (k : ℕ) (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    UpperHalfPlane.petersson (k : ℤ) F F z = (‖F z‖^2*z.im^k : ℝ) := by
  rw [UpperHalfPlane.petersson,zpow_natCast,← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq]
  push_cast
  rfl

theorem spectralPetersson_self_integrable (k : ℕ) (F : UpperHalfPlane → ℂ)
    (hF : Integrable (fun z => UpperHalfPlane.petersson (k : ℤ) F F z)) :
    Integrable (fun z => ‖F z‖^2*z.im^k) := by
  have h := hF.norm
  simpa only [spectralPetersson_self_pair,Complex.norm_real,
    Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg (UpperHalfPlane.im_pos _).le _))] using h

end ArtinMatthews
