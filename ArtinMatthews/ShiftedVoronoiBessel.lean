module

public import Mathlib.Analysis.SpecialFunctions.Bessel


set_option backward.privateInPublic true
@[expose] public section

/-!
# The actual order-zero Bessel series for the Voronoi kernel

This identifies Mathlib's hypergeometric definition of `J₀` with its convergent
factorial series. It is a starting point for the Bessel integral calculation;
no Laplace integral, Mellin integral, or Voronoi summation formula is assumed.
-/

noncomputable section

namespace ArtinMatthews

/-- The factorial series for the actual complex Bessel function `J₀`. -/
theorem hasSum_besselJ_zero (z : ℂ) :
    HasSum (fun n : ℕ ↦ (-((z / 2) ^ 2)) ^ n / (n.factorial : ℂ) ^ 2)
      (Complex.besselJ 0 z) := by
  have hs := (Complex.regularizedHGFunSeries 0 {(1 : ℂ)}).hasSum
    (x := -((z / 2) ^ 2)) (by simp)
  simpa [Complex.besselJ, Complex.regularizedHGFun,
    Complex.regularizedHGFunSeries, Complex.regularizedHGFunCoeff,
    add_comm (1 : ℂ), Complex.Gamma_nat_eq_factorial, pow_two, div_eq_mul_inv] using hs

/-- The square-root argument used by the Voronoi kernel removes the square
from the Bessel series without a branch choice. -/
theorem hasSum_besselJ_zero_sqrt (t : ℝ) (ht : 0 ≤ t) :
    HasSum (fun n : ℕ ↦ (-(t : ℂ)) ^ n / (n.factorial : ℂ) ^ 2)
      (Complex.besselJ 0 (2 * (Real.sqrt t : ℂ))) := by
  simpa only [mul_div_cancel_left₀ _ (two_ne_zero : (2 : ℂ) ≠ 0),
    ← Complex.ofReal_pow, Real.sq_sqrt ht] using
    hasSum_besselJ_zero (2 * (Real.sqrt t : ℂ))

end ArtinMatthews
