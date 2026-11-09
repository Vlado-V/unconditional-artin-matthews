module

public import ArtinMatthews.MarkedProgressionIndexed
public import ArtinMatthews.MarkedProgressionCoprime
public import ArtinMatthews.MarkedProgressionScaling


set_option backward.privateInPublic true
@[expose] public section

/-! Removing the local coprimality factors from the main terms of a finite
indexed divisor polynomial. Coefficient signs are retained exactly, and
both rounding and coprimality losses remain explicit. -/

namespace ArtinMatthews

open MeasureTheory
open scoped BigOperators

variable {ι : Type*}

/-- A single progression loses only terms whose represented divisor shares
at least one prime with its modulus. -/
theorem marked_indexed_main_term_error (D : Finset ι) (d : ι → ℕ)
    (c : ι → ℝ) (I : ℝ) (r : ℕ) :
    |(∑ j ∈ D, c j * (if (d j).Coprime r then I / (d j * r : ℕ) else 0)) -
      (I / (r : ℝ)) * ∑ j ∈ D, c j / (d j : ℝ)| ≤
      ∑ j ∈ D, (|I| * (|c j| / (d j : ℝ))) *
        (if ¬(d j).Coprime r then 1 / (r : ℝ) else 0) := by
  classical
  have hmain : (I / (r : ℝ)) * (∑ j ∈ D, c j / (d j : ℝ)) =
      ∑ j ∈ D, c j * (I / (d j * r : ℕ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Nat.cast_mul, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hmain, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ D).trans_eq
  apply Finset.sum_congr rfl
  intro j _
  by_cases hcop : (d j).Coprime r
  · rw [ite_eq_left hcop, ite_eq_right (not_not_intro hcop)]
    simp
  · rw [ite_eq_right hcop, ite_eq_left hcop]
    simp [abs_mul, Nat.cast_mul, div_eq_mul_inv, mul_inv_rev]
    ring

/-- Summing the discarded local factors costs the harmonic mass of moduli
sharing a prime with each represented divisor. -/
theorem marked_indexed_main_summed_error (R : ℕ) (D : Finset ι)
    (d : ι → ℕ) (c : ι → ℝ) (hD : ∀ j ∈ D, 0 < d j) (I : ℝ) :
    (∑ r ∈ Finset.Icc 1 R,
      |(∑ j ∈ D, c j * (if (d j).Coprime r then I / (d j * r : ℕ) else 0)) -
        (I / (r : ℝ)) * ∑ j ∈ D, c j / (d j : ℝ)|) ≤
      |I| * (harmonic R : ℝ) *
        ∑ j ∈ D, (|c j| / (d j : ℝ)) * ∑ p ∈ (d j).primeFactors, 1 / (p : ℝ) := by
  classical
  calc
    _ ≤ ∑ r ∈ Finset.Icc 1 R, ∑ j ∈ D,
        (|I| * (|c j| / (d j : ℝ))) *
          (if ¬(d j).Coprime r then 1 / (r : ℝ) else 0) :=
      Finset.sum_le_sum fun r _ => marked_indexed_main_term_error D d c I r
    _ = ∑ j ∈ D, (|I| * (|c j| / (d j : ℝ))) *
        ∑ r ∈ Finset.Icc 1 R, if ¬(d j).Coprime r then 1 / (r : ℝ) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
    _ ≤ ∑ j ∈ D, (|I| * (|c j| / (d j : ℝ))) *
        ((harmonic R : ℝ) * ∑ p ∈ (d j).primeFactors, 1 / (p : ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      have h := noncoprime_reciprocal_sum_le_harmonic R (d j) (hD j hj)
      rw [Finset.sum_filter] at h
      exact mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- The actual polynomial progression remainder, with the unrestricted
main term and both independent sources of error displayed. -/
theorem marked_indexed_polynomial_unrestricted_error (R : ℕ) (D : Finset ι)
    (d : ι → ℕ) (c : ι → ℝ) (hD : ∀ j ∈ D, 0 < d j)
    (f : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) (hf : Differentiable ℝ f)
    (hderiv : Continuous (deriv f)) (hfT : f T = 0) :
    (∑ r ∈ Finset.Icc 1 R,
      |(∑ u ∈ (Finset.Icc 0 ⌊T⌋₊).filter (fun u => r ∣ u + 1),
          f u * markedIndexedDivisorPolynomial D d c u) -
        ((∫ t in Set.Ioc 0 T, f t) / (r : ℝ)) * ∑ j ∈ D, c j / (d j : ℝ)|) ≤
      (R : ℝ) * (3 * ∫ t in Set.Ioc 0 T, |deriv f t|) * ∑ j ∈ D, |c j| +
        |∫ t in Set.Ioc 0 T, f t| * (harmonic R : ℝ) *
          ∑ j ∈ D, (|c j| / (d j : ℝ)) *
            ∑ p ∈ (d j).primeFactors, 1 / (p : ℝ) := by
  classical
  have hround := marked_indexed_polynomial_summed_error (Finset.Icc 1 R) D d c
    (fun r hr => (Finset.mem_Icc.mp hr).1) hD f hT hf hderiv hfT
  have hlocal := marked_indexed_main_summed_error R D d c hD (∫ t in Set.Ioc 0 T, f t)
  have htriangle :
      (∑ r ∈ Finset.Icc 1 R,
        |(∑ u ∈ (Finset.Icc 0 ⌊T⌋₊).filter (fun u => r ∣ u + 1),
            f u * markedIndexedDivisorPolynomial D d c u) -
          ((∫ t in Set.Ioc 0 T, f t) / (r : ℝ)) * ∑ j ∈ D, c j / (d j : ℝ)|) ≤
      (∑ r ∈ Finset.Icc 1 R,
        |(∑ u ∈ (Finset.Icc 0 ⌊T⌋₊).filter (fun u => r ∣ u + 1),
            f u * markedIndexedDivisorPolynomial D d c u) -
          ∑ j ∈ D, c j * (if (d j).Coprime r then
            (∫ t in Set.Ioc 0 T, f t) / (d j * r : ℕ) else 0)|) +
      (∑ r ∈ Finset.Icc 1 R,
        |(∑ j ∈ D, c j * (if (d j).Coprime r then
            (∫ t in Set.Ioc 0 T, f t) / (d j * r : ℕ) else 0)) -
          ((∫ t in Set.Ioc 0 T, f t) / (r : ℝ)) * ∑ j ∈ D, c j / (d j : ℝ)|) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro r _
    exact abs_sub_le _ _ _
  apply htriangle.trans
  simpa using add_le_add hround hlocal

/-- At scale `x`, rounding depends on the unscaled test variation and the
coprimality loss has exactly the scale of the main integral. -/
theorem marked_indexed_polynomial_rescaled_unrestricted_error (R : ℕ) (D : Finset ι)
    (d : ι → ℕ) (c : ι → ℝ) (hD : ∀ j ∈ D, 0 < d j)
    (Φ : ℝ → ℝ) {x T : ℝ} (hx : 0 < x) (hT : 0 ≤ T)
    (hΦ : Differentiable ℝ Φ) (hderiv : Continuous (deriv Φ)) (hΦT : Φ T = 0) :
    (∑ r ∈ Finset.Icc 1 R,
      |(∑ u ∈ (Finset.Icc 0 ⌊T * x⌋₊).filter (fun u => r ∣ u + 1),
          Φ ((u : ℝ) / x) * markedIndexedDivisorPolynomial D d c u) -
        ((x * ∫ t in Set.Ioc 0 T, Φ t) / (r : ℝ)) * ∑ j ∈ D, c j / (d j : ℝ)|) ≤
      (R : ℝ) * (3 * ∫ t in Set.Ioc 0 T, |deriv Φ t|) * ∑ j ∈ D, |c j| +
        (x * |∫ t in Set.Ioc 0 T, Φ t|) * (harmonic R : ℝ) *
          ∑ j ∈ D, (|c j| / (d j : ℝ)) *
            ∑ p ∈ (d j).primeFactors, 1 / (p : ℝ) := by
  have h := marked_indexed_polynomial_unrestricted_error R D d c hD
    (fun u => Φ (u / x)) (mul_nonneg hT hx.le) (marked_rescale_differentiable Φ x hΦ)
    (marked_rescale_deriv_continuous Φ x hΦ hderiv)
    (by rw [marked_rescale_endpoint Φ hx T, hΦT])
  rw [marked_rescale_integral Φ hx hT, marked_rescale_variation Φ hx hT hΦ,
    abs_mul, abs_of_pos hx] at h
  exact h

end ArtinMatthews
