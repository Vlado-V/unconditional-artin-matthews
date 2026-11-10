module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import ArtinMatthews.MarkedProgressionSmooth
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.Tactic.Basify
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

/-!
# Smooth progression errors for finite represented-divisor polynomials

This is the summation step after the marking weights have been expanded
and truncated. The complete coefficient mass is retained explicitly;
no smallness or divisor-level bound is assumed implicitly.
-/

namespace ArtinMatthews

open MeasureTheory
open scoped BigOperators

noncomputable def markedDivisorPolynomial (D : Finset ℕ) (c : ℕ → ℝ) (u : ℕ) : ℝ :=
  ∑ d ∈ D, if d ∣ u then c d else 0

/-- Exact interchange of the divisor expansion and progression sum. -/
theorem markedDivisorPolynomial_sum (U D : Finset ℕ) (c : ℕ → ℝ)
    (f : ℕ → ℝ) (r : ℕ) :
    (∑ u ∈ U.filter (fun u => r ∣ u + 1), f u * markedDivisorPolynomial D c u) =
      ∑ d ∈ D, c d * ∑ u ∈ U.filter (fun u => d ∣ u ∧ r ∣ u + 1), f u := by
  classical
  unfold markedDivisorPolynomial
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hru : r ∣ u + 1 <;> by_cases hdu : d ∣ u <;> simp [hru, hdu, mul_comm]

/-- Uniform smooth remainder for a finite divisor polynomial. -/
theorem marked_polynomial_smooth_error (D : Finset ℕ) (c : ℕ → ℝ)
    (hD : ∀ d ∈ D, 0 < d) (r : ℕ) (hr : 0 < r)
    (f : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) (hf : Differentiable ℝ f)
    (hderiv : Continuous (deriv f)) (hfT : f T = 0) :
    |(∑ u ∈ (Finset.Icc 0 ⌊T⌋₊).filter (fun u => r ∣ u + 1),
        f u * markedDivisorPolynomial D c u) -
      (∑ d ∈ D, c d * (if d.Coprime r then
        (∫ t in Set.Ioc 0 T, f t) / (d * r : ℕ) else 0))| ≤
      (3 * ∫ t in Set.Ioc 0 T, |deriv f t|) * ∑ d ∈ D, |c d| := by
  classical
  rw [markedDivisorPolynomial_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ d ∈ D, |c d *
        ((∑ u ∈ (Finset.Icc 0 ⌊T⌋₊).filter (fun u => d ∣ u ∧ r ∣ u + 1), f u) -
          (if d.Coprime r then (∫ t in Set.Ioc 0 T, f t) / (d * r : ℕ) else 0))| := by
      have h := Finset.abs_sum_le_sum_abs (fun d =>
        c d * (∑ u ∈ (Finset.Icc 0 ⌊T⌋₊).filter (fun u => d ∣ u ∧ r ∣ u + 1), f u) -
        c d * (if d.Coprime r then (∫ t in Set.Ioc 0 T, f t) / (d * r : ℕ) else 0)) D
      simpa only [mul_sub] using h
    _ ≤ ∑ d ∈ D, |c d| * (3 * ∫ t in Set.Ioc 0 T, |deriv f t|) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (marked_divisor_smooth_error d r (hD d hd) hr f hT hf hderiv hfT) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- Summing all progression errors costs the number of moduli times the
explicit coefficient mass and test variation. -/
theorem marked_polynomial_summed_error (R D : Finset ℕ) (c : ℕ → ℝ)
    (hR : ∀ r ∈ R, 0 < r) (hD : ∀ d ∈ D, 0 < d)
    (f : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) (hf : Differentiable ℝ f)
    (hderiv : Continuous (deriv f)) (hfT : f T = 0) :
    (∑ r ∈ R, |(∑ u ∈ (Finset.Icc 0 ⌊T⌋₊).filter (fun u => r ∣ u + 1),
        f u * markedDivisorPolynomial D c u) -
      (∑ d ∈ D, c d * (if d.Coprime r then
        (∫ t in Set.Ioc 0 T, f t) / (d * r : ℕ) else 0))|) ≤
      (R.card : ℝ) * (3 * ∫ t in Set.Ioc 0 T, |deriv f t|) * ∑ d ∈ D, |c d| := by
  calc
    _ ≤ ∑ _r ∈ R, (3 * ∫ t in Set.Ioc 0 T, |deriv f t|) * ∑ d ∈ D, |c d| :=
      Finset.sum_le_sum (fun r hr => marked_polynomial_smooth_error D c hD r (hR r hr) f hT hf hderiv hfT)
    _ = _ := by simp [mul_assoc]

end ArtinMatthews
