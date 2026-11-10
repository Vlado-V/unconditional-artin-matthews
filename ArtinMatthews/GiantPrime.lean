module

public import ArtinMatthews.DivisorBound
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset


set_option backward.privateInPublic true
@[expose] public section

/-! The giant-prime divisor statistic is zero or one on its required support. -/

namespace ArtinMatthews

/-- Two distinct prime divisors above a square-root threshold cannot occur. -/
theorem card_primeFactorsAbove_le_one {n : ℕ} {y : ℝ}
    (hn : 0 < n) (hy : 0 ≤ y) (hny : (n : ℝ) ≤ y ^ 2) :
    (primeFactorsAbove n y).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp q hq
  by_contra hpq
  obtain ⟨hpp, hpd, _, hpy⟩ := mem_primeFactorsAbove.mp hp
  obtain ⟨hqp, hqd, _, hqy⟩ := mem_primeFactorsAbove.mp hq
  have hcop : p.Coprime q := hpp.coprime_iff_not_dvd.mpr (by
    intro hd
    exact hpq ((Nat.dvd_prime hqp).mp hd |>.resolve_left hpp.ne_one))
  have hpqd : p * q ∣ n := hcop.mul_dvd_of_dvd_of_dvd hpd hqd
  have hle : (p : ℝ) * (q : ℝ) ≤ n := by exact_mod_cast Nat.le_of_dvd hn hpqd
  have hlt : y ^ 2 < (p : ℝ) * (q : ℝ) := by nlinarith
  linarith

lemma giant_threshold_sq {x ε : ℝ} (hx : 4 ≤ x) (hε : ε ≤ 1 / 4) :
    2 * x ≤ (x ^ (1 - ε)) ^ 2 := by
  have hx0 : 0 ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  have hsqrt : 2 ≤ x ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact (Real.le_sqrt (by norm_num) hx0).mpr (by norm_num; exact hx)
  calc
    2 * x ≤ x * x ^ (1 / 2 : ℝ) := by nlinarith
    _ = x ^ (1 + 1 / 2 : ℝ) := by rw [Real.rpow_add hxpos, Real.rpow_one]
    _ ≤ x ^ ((1 - ε) * 2) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ = (x ^ (1 - ε)) ^ 2 := by rw [Real.rpow_mul hx0, Real.rpow_two]

/-- The prime-factor window in (1.2), expressed by finite prime divisors. -/
noncomputable def giantPrimeFactors (n : ℕ) (x ε : ℝ) : Finset ℕ := by
  classical
  exact (primeFactorsAbove n (x ^ (1 - ε))).filter
    (fun p => (p : ℝ) ≤ x ^ (1 - ε / 2))

/-- On the support `0 < n ≤ 2x`, the statistic in (1.2) is at most one. -/
theorem giantPrimeFactors_card_le_one {n : ℕ} {x ε : ℝ}
    (hn : 0 < n) (hnx : (n : ℝ) ≤ 2 * x) (hx : 4 ≤ x) (hε : ε ≤ 1 / 4) :
    (giantPrimeFactors n x ε).card ≤ 1 := by
  classical
  apply le_trans (Finset.card_filter_le _ _)
  apply card_primeFactorsAbove_le_one hn
  · exact Real.rpow_nonneg (by linarith) _
  · exact hnx.trans (giant_threshold_sq hx hε)

/-- The exact zero-or-one alternative used for the weighted prime count. -/
theorem giantPrimeFactors_card_zero_or_one {n : ℕ} {x ε : ℝ}
    (hn : 0 < n) (hnx : (n : ℝ) ≤ 2 * x) (hx : 4 ≤ x) (hε : ε ≤ 1 / 4) :
    (giantPrimeFactors n x ε).card = 0 ∨ (giantPrimeFactors n x ε).card = 1 := by
  have := giantPrimeFactors_card_le_one hn hnx hx hε
  omega

end ArtinMatthews
