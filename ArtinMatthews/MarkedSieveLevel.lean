module

public import ArtinMatthews.MarkedEstimateSieve
public import ArtinMatthews.MarkedEstimateSieveParameters


set_option backward.privateInPublic true
@[expose] public section

/-! The actual finite sieve divisor level lies inside the progression range
when the power cutoff is chosen by the already proved parameter formula. -/

namespace ArtinMatthews

open OAI.Erdos970.NumberTheoryLean

/-- Exact floor-power level comparison, with no asymptotic assumption. -/
theorem marked_floor_power_le (x γ c : ℝ) (N : ℕ)
    (hx : 1 ≤ x) (hlevel : γ * (N : ℝ) ≤ c) :
    ⌊x ^ γ⌋₊ ^ N ≤ ⌊x ^ c⌋₊ := by
  apply (Nat.le_floor_iff (Real.rpow_nonneg (le_trans zero_le_one hx) c)).mpr
  rw [Nat.cast_pow]
  calc
    (⌊x ^ γ⌋₊ : ℝ) ^ N ≤ (x ^ γ) ^ N :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le (Real.rpow_nonneg (le_trans zero_le_one hx) γ)) N
    _ = x ^ (γ * (N : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_trans zero_le_one hx)]
    _ ≤ x ^ c := Real.rpow_le_rpow_of_exponent_le hx hlevel

/-- Every divisor entering the proved fundamental sieve is a positive
modulus in the full available progression range. -/
theorem marked_sieve_level_subset (P : Finset ℕ) (x γ c : ℝ) (N : ℕ)
    (hx : 1 ≤ x) (hlevel : γ * (N : ℝ) ≤ c) :
    FundamentalBlockEstimate.levelDivisors P (⌊x ^ γ⌋₊ ^ N) ⊆ Finset.Icc 1 ⌊x ^ c⌋₊ := by
  intro d hd
  obtain ⟨hdiv, hsize⟩ := Finset.mem_filter.mp hd
  exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hdiv,
    hsize.trans (marked_floor_power_le x γ c N hx hlevel)⟩

/-- The fixed positive sieve exponent leaves half of the available
progression exponent in reserve. -/
theorem marked_sieve_parameter_level_subset (P : Finset ℕ) (x c : ℝ) (m : ℕ)
    (hx : 1 ≤ x) (hc : 0 ≤ c) :
    FundamentalBlockEstimate.levelDivisors P
      (⌊x ^ markedSieveExponent c m⌋₊ ^ (12 * (m + 1))) ⊆ Finset.Icc 1 ⌊x ^ c⌋₊ := by
  apply marked_sieve_level_subset P x (markedSieveExponent c m) c (12 * (m + 1)) hx
  have heq := markedSieveExponent_level c m
  push_cast
  nlinarith

end ArtinMatthews
