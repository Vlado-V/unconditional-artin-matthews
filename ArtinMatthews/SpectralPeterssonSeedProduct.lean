module

public import ArtinMatthews.SpectralHolomorphicCuspSeed
public import ArtinMatthews.SpectralPeterssonFourierAtHeight
public import ArtinMatthews.SpectralCuspDiagonalFourierIntegral


set_option backward.privateInPublic true
@[expose] public section

/-! Exact horizontal Fourier factors in the physical norm of a
holomorphic seed packet. -/
noncomputable section
open Set MeasureTheory UpperHalfPlane
open scoped ComplexConjugate

namespace ArtinMatthews

theorem spectralHolomorphicCuspSeed_pair (m n : ℕ+) (z : UpperHalfPlane) :
    conj (spectralHolomorphicCuspSeed (m : ℕ) z)*spectralHolomorphicCuspSeed (n : ℕ) z =
      atkinPhase (((n : ℝ)-(m : ℝ))*z.re)*
        (Real.exp (-(2*Real.pi*((m : ℝ)+(n : ℝ))*z.im)) : ℂ) := by
  unfold spectralHolomorphicCuspSeed atkinPhase
  rw [← Complex.exp_conj,← Complex.exp_add,Complex.ofReal_exp,← Complex.exp_add]
  congr 1
  apply Complex.ext <;>
    simp [Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im] <;> ring

theorem spectralPeterssonPhase_integral (d : ℤ) :
    (∫ x in Ioc (0 : ℝ) 1, atkinPhase ((d : ℝ)*x)) = if d = 0 then 1 else 0 := by
  have he : (fun x : ℝ => atkinPhase ((d : ℝ)*x)) = cuspFourierPhase 1 (-d) := by
    funext x
    rw [cuspFourierPhase_as_atkinPhase]
    congr 1
    push_cast
    ring
  rw [he,← intervalIntegral.integral_of_le zero_le_one]
  simpa only [neg_eq_zero,Complex.ofReal_one] using cuspFourierPhase_integral_full_period 1 zero_lt_one (-d)

end ArtinMatthews
