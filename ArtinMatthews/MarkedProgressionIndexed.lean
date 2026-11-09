module

public import ArtinMatthews.MarkedProgressionPolynomial


set_option backward.privateInPublic true
@[expose] public section

/-!
# Smooth progression errors for indexed divisor polynomials

This is the summation step after the marking weights have been expanded
and truncated. The complete coefficient mass is retained explicitly;
no smallness or divisor-level bound is assumed implicitly.
-/

namespace ArtinMatthews

variable {ι : Type*}

open MeasureTheory
open scoped BigOperators

noncomputable def markedIndexedDivisorPolynomial (D : Finset ι) (d : ι → ℕ) (c : ι → ℝ) (u : ℕ) : ℝ :=
  ∑ j ∈ D, if d j ∣ u then c j else 0

/-- Exact interchange of the divisor expansion and progression sum. -/
theorem markedIndexedDivisorPolynomial_sum (U : Finset ℕ) (D : Finset ι) (d : ι → ℕ) (c : ι → ℝ)
    (f : ℕ → ℝ) (r : ℕ) :
    (∑ u ∈ U.filter (fun u => r ∣ u + 1), f u * markedIndexedDivisorPolynomial D d c u) =
      ∑ j ∈ D, c j * ∑ u ∈ U.filter (fun u => d j ∣ u ∧ r ∣ u + 1), f u := by
  classical
  unfold markedIndexedDivisorPolynomial
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hru : r ∣ u + 1 <;> by_cases hdu : d j ∣ u <;> simp [hru, hdu, mul_comm]

/-- Uniform smooth remainder for a finite divisor polynomial. -/
theorem marked_indexed_polynomial_smooth_error (D : Finset ι) (d : ι → ℕ) (c : ι → ℝ)
    (hD : ∀ j ∈ D, 0 < d j) (r : ℕ) (hr : 0 < r)
    (f : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) (hf : Differentiable ℝ f)
    (hderiv : Continuous (deriv f)) (hfT : f T = 0) :
    |(∑ u ∈ (Finset.Icc 0 ⌊T⌋₊).filter (fun u => r ∣ u + 1),
        f u * markedIndexedDivisorPolynomial D d c u) -
      (∑ j ∈ D, c j * (if (d j).Coprime r then
        (∫ t in Set.Ioc 0 T, f t) / (d j * r : ℕ) else 0))| ≤
      (3 * ∫ t in Set.Ioc 0 T, |deriv f t|) * ∑ j ∈ D, |c j| := by
  classical
  rw [markedIndexedDivisorPolynomial_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ D, |c j *
        ((∑ u ∈ (Finset.Icc 0 ⌊T⌋₊).filter (fun u => d j ∣ u ∧ r ∣ u + 1), f u) -
          (if (d j).Coprime r then (∫ t in Set.Ioc 0 T, f t) / (d j * r : ℕ) else 0))| := by
      have h := Finset.abs_sum_le_sum_abs (fun j =>
        c j * (∑ u ∈ (Finset.Icc 0 ⌊T⌋₊).filter (fun u => d j ∣ u ∧ r ∣ u + 1), f u) -
        c j * (if (d j).Coprime r then (∫ t in Set.Ioc 0 T, f t) / (d j * r : ℕ) else 0)) D
      simpa only [mul_sub] using h
    _ ≤ ∑ j ∈ D, |c j| * (3 * ∫ t in Set.Ioc 0 T, |deriv f t|) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (marked_divisor_smooth_error (d j) r (hD j hj) hr f hT hf hderiv hfT) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- Summing all progression errors costs the number of moduli times the
explicit coefficient mass and test variation. -/
theorem marked_indexed_polynomial_summed_error (R : Finset ℕ) (D : Finset ι) (d : ι → ℕ) (c : ι → ℝ)
    (hR : ∀ r ∈ R, 0 < r) (hD : ∀ j ∈ D, 0 < d j)
    (f : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) (hf : Differentiable ℝ f)
    (hderiv : Continuous (deriv f)) (hfT : f T = 0) :
    (∑ r ∈ R, |(∑ u ∈ (Finset.Icc 0 ⌊T⌋₊).filter (fun u => r ∣ u + 1),
        f u * markedIndexedDivisorPolynomial D d c u) -
      (∑ j ∈ D, c j * (if (d j).Coprime r then
        (∫ t in Set.Ioc 0 T, f t) / (d j * r : ℕ) else 0))|) ≤
      (R.card : ℝ) * (3 * ∫ t in Set.Ioc 0 T, |deriv f t|) * ∑ j ∈ D, |c j| := by
  calc
    _ ≤ ∑ _r ∈ R, (3 * ∫ t in Set.Ioc 0 T, |deriv f t|) * ∑ j ∈ D, |c j| :=
      Finset.sum_le_sum (fun r hr => marked_indexed_polynomial_smooth_error D d c hD r (hR r hr) f hT hf hderiv hfT)
    _ = _ := by simp [mul_assoc]

end ArtinMatthews
