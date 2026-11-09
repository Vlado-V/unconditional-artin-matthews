module

public import ArtinMatthews.MarkedProgressionIndexed
public import ArtinMatthews.MarkedProgressionCoprime
public import ArtinMatthews.MarkedProgressionScaling


set_option backward.privateInPublic true
@[expose] public section

/-! Positive remainder polynomials can be averaged by their unrestricted
reciprocal mass without paying a coprimality correction. -/

namespace ArtinMatthews

open MeasureTheory
open scoped BigOperators

variable {ι : Type*}

/-- Actual smooth progression upper bound for a polynomial with nonnegative
coefficients. The main term has no local coprimality restriction. -/
theorem marked_positive_polynomial_upper (D : Finset ι) (d : ι → ℕ) (c : ι → ℝ)
    (hD : ∀ j ∈ D, 0 < d j) (hc : ∀ j ∈ D, 0 ≤ c j) (r : ℕ) (hr : 0 < r)
    (f : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) (hf : Differentiable ℝ f)
    (hderiv : Continuous (deriv f)) (hfT : f T = 0)
    (hI : 0 ≤ ∫ t in Set.Ioc 0 T, f t) :
    (∑ u ∈ (Finset.Icc 0 ⌊T⌋₊).filter (fun u => r ∣ u + 1),
        f u * markedIndexedDivisorPolynomial D d c u) ≤
      ((∫ t in Set.Ioc 0 T, f t) / (r : ℝ)) * (∑ j ∈ D, c j / (d j : ℝ)) +
        (3 * ∫ t in Set.Ioc 0 T, |deriv f t|) * ∑ j ∈ D, c j := by
  classical
  have herr := (abs_le.mp (marked_indexed_polynomial_smooth_error D d c hD r hr
    f hT hf hderiv hfT)).2
  have hmain : (∑ j ∈ D, c j * (if (d j).Coprime r then
      (∫ t in Set.Ioc 0 T, f t) / (d j * r : ℕ) else 0)) ≤
      ((∫ t in Set.Ioc 0 T, f t) / (r : ℝ)) * (∑ j ∈ D, c j / (d j : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hpos : 0 ≤ (∫ t in Set.Ioc 0 T, f t) / (d j * r : ℕ) := div_nonneg hI (Nat.cast_nonneg _)
    calc
      _ ≤ c j * ((∫ t in Set.Ioc 0 T, f t) / (d j * r : ℕ)) := by
        apply mul_le_mul_of_nonneg_left _ (hc j hj)
        split_ifs <;> simp_all
      _ = _ := by simp only [Nat.cast_mul, div_eq_mul_inv, mul_inv_rev]; ring
  have habs : (∑ j ∈ D, |c j|) = ∑ j ∈ D, c j :=
    Finset.sum_congr rfl (fun j hj => abs_of_nonneg (hc j hj))
  rw [habs] at herr
  linarith

/-- Summing positive tails costs only harmonic mass in the main term and
linear modulus count in the exact rounding error. -/
theorem marked_positive_polynomial_summed_upper (R : ℕ) (D : Finset ι)
    (d : ι → ℕ) (c : ι → ℝ) (hD : ∀ j ∈ D, 0 < d j) (hc : ∀ j ∈ D, 0 ≤ c j)
    (f : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) (hf : Differentiable ℝ f)
    (hderiv : Continuous (deriv f)) (hfT : f T = 0)
    (hI : 0 ≤ ∫ t in Set.Ioc 0 T, f t) :
    (∑ r ∈ Finset.Icc 1 R, ∑ u ∈ (Finset.Icc 0 ⌊T⌋₊).filter (fun u => r ∣ u + 1),
        f u * markedIndexedDivisorPolynomial D d c u) ≤
      ((∫ t in Set.Ioc 0 T, f t) * (harmonic R : ℝ)) * (∑ j ∈ D, c j / (d j : ℝ)) +
        (R : ℝ) * (3 * ∫ t in Set.Ioc 0 T, |deriv f t|) * ∑ j ∈ D, c j := by
  calc
    _ ≤ ∑ r ∈ Finset.Icc 1 R,
        (((∫ t in Set.Ioc 0 T, f t) / (r : ℝ)) * (∑ j ∈ D, c j / (d j : ℝ)) +
          (3 * ∫ t in Set.Ioc 0 T, |deriv f t|) * (∑ j ∈ D, c j)) :=
      Finset.sum_le_sum (fun r hr => marked_positive_polynomial_upper D d c hD hc r
        (Finset.mem_Icc.mp hr).1 f hT hf hderiv hfT hI)
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      have hsum : (∑ r ∈ Finset.Icc 1 R, (∫ t in Set.Ioc 0 T, f t) / (r : ℝ)) =
          (∫ t in Set.Ioc 0 T, f t) * (harmonic R : ℝ) := by
        rw [← reciprocal_Icc_eq_harmonic, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        ring
      rw [hsum]
      simp [mul_assoc]

end ArtinMatthews
