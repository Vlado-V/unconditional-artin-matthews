module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import ArtinMatthews.MarkedProgressionSmooth
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! Exact dilation identities for the smooth represented-divisor progression
estimate. The scale disappears from the total-variation error; the main
integral acquires exactly the factor `x`. -/

namespace ArtinMatthews

open MeasureTheory
open scoped BigOperators

/-- Differentiability is preserved by dilation of the argument. -/
theorem marked_rescale_differentiable (Φ : ℝ → ℝ) (x : ℝ)
    (hΦ : Differentiable ℝ Φ) :
    Differentiable ℝ (fun u => Φ (u / x)) :=
  hΦ.comp (differentiable_id.div_const x)

/-- The chain rule retains the exact inverse scale. -/
theorem marked_rescale_deriv (Φ : ℝ → ℝ) (x : ℝ)
    (hΦ : Differentiable ℝ Φ) (u : ℝ) :
    deriv (fun v => Φ (v / x)) u = deriv Φ (u / x) / x := by
  simpa only [Function.comp_def, id_eq, div_eq_mul_inv, one_mul] using
    ((hΦ (u / x)).hasDerivAt.comp u ((hasDerivAt_id u).div_const x)).deriv

/-- Continuous first derivatives are preserved by dilation. -/
theorem marked_rescale_deriv_continuous (Φ : ℝ → ℝ) (x : ℝ)
    (hΦ : Differentiable ℝ Φ) (hderiv : Continuous (deriv Φ)) :
    Continuous (deriv (fun u => Φ (u / x))) := by
  have heq : deriv (fun u => Φ (u / x)) = fun u => deriv Φ (u / x) / x :=
    funext (marked_rescale_deriv Φ x hΦ)
  rw [heq]
  exact (hderiv.comp (continuous_id.div_const x)).div_const x

/-- The right endpoint of the dilated interval is evaluated exactly. -/
theorem marked_rescale_endpoint (Φ : ℝ → ℝ) {x : ℝ} (hx : 0 < x) (T : ℝ) :
    Φ ((T * x) / x) = Φ T := by
  rw [mul_div_cancel_right₀ T hx.ne']

/-- Exact change of variables for the finite-interval main term. -/
theorem marked_rescale_integral (Φ : ℝ → ℝ) {x T : ℝ}
    (hx : 0 < x) (hT : 0 ≤ T) :
    (∫ u in Set.Ioc 0 (T * x), Φ (u / x)) =
      x * ∫ t in Set.Ioc 0 T, Φ t := by
  have h := intervalIntegral.integral_comp_div (a := 0) (b := T * x) Φ hx.ne'
  simpa only [zero_div, mul_div_cancel_right₀ T hx.ne', smul_eq_mul,
    intervalIntegral.integral_of_le (mul_nonneg hT hx.le),
    intervalIntegral.integral_of_le hT] using h

/-- The integrated absolute derivative is invariant under positive dilation. -/
theorem marked_rescale_variation (Φ : ℝ → ℝ) {x T : ℝ}
    (hx : 0 < x) (hT : 0 ≤ T) (hΦ : Differentiable ℝ Φ) :
    (∫ u in Set.Ioc 0 (T * x), |deriv (fun v => Φ (v / x)) u|) =
      ∫ t in Set.Ioc 0 T, |deriv Φ t| := by
  simp_rw [marked_rescale_deriv Φ x hΦ, abs_div, abs_of_pos hx]
  rw [integral_div, marked_rescale_integral (fun t => |deriv Φ t|) hx hT]
  exact mul_div_cancel_left₀ _ hx.ne'

/-- The represented-divisor estimate at scale `x`, with a scale-independent
error. All arithmetic distribution information comes from the proved CRT
count and Abel summation in `marked_divisor_smooth_error`. -/
theorem marked_divisor_rescaled_smooth_error (d r : ℕ)
    (hd : 0 < d) (hr : 0 < r) (Φ : ℝ → ℝ) {x T : ℝ}
    (hx : 0 < x) (hT : 0 ≤ T) (hΦ : Differentiable ℝ Φ)
    (hderiv : Continuous (deriv Φ)) (hΦT : Φ T = 0) :
    |(∑ k ∈ (Finset.Icc 0 ⌊T * x⌋₊).filter (fun k => d ∣ k ∧ r ∣ k + 1),
        Φ ((k : ℝ) / x)) -
      (if d.Coprime r then (x * ∫ t in Set.Ioc 0 T, Φ t) / (d * r : ℕ)
       else 0)| ≤ 3 * ∫ t in Set.Ioc 0 T, |deriv Φ t| := by
  have h := marked_divisor_smooth_error d r hd hr (fun u => Φ (u / x))
    (mul_nonneg hT hx.le) (marked_rescale_differentiable Φ x hΦ)
    (marked_rescale_deriv_continuous Φ x hΦ hderiv)
    (by rw [marked_rescale_endpoint Φ hx T, hΦT])
  rw [marked_rescale_integral Φ hx hT, marked_rescale_variation Φ hx hT hΦ] at h
  exact h

end ArtinMatthews
