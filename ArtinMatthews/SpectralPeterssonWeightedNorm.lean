module

public import ArtinMatthews.SpectralHolomorphicCuspSeed


set_option backward.privateInPublic true
@[expose] public section

/-! The actual weight-k slash has unit modulus in the Petersson-weighted
physical norm. This keeps the slash phases in the cut packet. -/
noncomputable section
open UpperHalfPlane
open scoped MatrixGroups

namespace ArtinMatthews

theorem spectralHolomorphicSlash_norm_sq_weight (k : ℕ) (G : SL(2, ℝ))
    (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    ‖spectralHolomorphicSlash k G F z‖^2*z.im^k = ‖F (G • z)‖^2*(G • z).im^k := by
  have hnorm (H : UpperHalfPlane → ℂ) (w : UpperHalfPlane) :
      ‖UpperHalfPlane.petersson (k : ℤ) H H w‖ = ‖H w‖^2*w.im^k := by
    simp only [UpperHalfPlane.petersson,norm_mul,Complex.norm_conj,zpow_natCast,norm_pow,
      Complex.norm_real,Real.norm_of_nonneg w.im_pos.le,pow_two]
  have h := congrArg (fun x : ℂ => ‖x‖) (spectralHolomorphicPetersson_slash k G F F z)
  simpa only [hnorm] using h

end ArtinMatthews
