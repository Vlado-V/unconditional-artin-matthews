module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic


set_option backward.privateInPublic true
@[expose] public section

/-!
# Exponential monomial integrals for the Bessel expansion

These evaluations supply the termwise Laplace integrals of the factorial
series for `J₀`.  The integral is computed from Mathlib's scaled Gamma
integral, and its strictly positive value also proves integrability.
-/

noncomputable section

open MeasureTheory Set

namespace ArtinMatthews

/-- The Laplace integral of a real monomial on the positive half-line. -/
theorem integral_pow_mul_exp_neg_mul_Ioi (a : ℝ) (ha : 0 < a) (n : ℕ) :
    (∫ x : ℝ in Ioi 0, x ^ n * Real.exp (-(a * x))) =
      (n.factorial : ℝ) / a ^ (n + 1) := by
  have key := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (n : ℝ) + 1) (r := a) (by positivity) ha
  simp only [add_sub_cancel_right, Real.rpow_natCast, Real.Gamma_nat_eq_factorial] at key
  rw [show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by simp, Real.rpow_natCast] at key
  simpa only [one_div, div_eq_mul_inv, one_mul, mul_one, inv_pow, mul_comm] using key

/-- Exponential damping makes every real monomial integrable on `(0, ∞)`. -/
theorem integrableOn_pow_mul_exp_neg_mul_Ioi (a : ℝ) (ha : 0 < a) (n : ℕ) :
    IntegrableOn (fun x : ℝ ↦ x ^ n * Real.exp (-(a * x))) (Ioi 0) := by
  exact .of_integral_ne_zero (by
    rw [integral_pow_mul_exp_neg_mul_Ioi a ha n]
    exact ne_of_gt (by positivity))

end ArtinMatthews
