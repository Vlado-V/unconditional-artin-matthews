module

public import ArtinMatthews.MarkedEstimateMertensBandCore
public import ArtinMatthews.MarkedTypeIICollisionDecay
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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


set_option backward.privateInPublic true
@[expose] public section

/-!
# Actual counting bound for shared marking primes

PD §3.1 and §4.9 discard numeric label products sharing a marking prime.
Among positive integers at most `N`, a prime `p` divides exactly `N/p`
entries. Taking the union over marking primes bounds the actual ordered
pair count by `N² Σ p⁻²`. The proved prime-band tail then gives every
fixed logarithmic saving, uniformly in the cutoff `N`.
-/

namespace ArtinMatthews

open Filter
open scoped BigOperators Topology

def markedLabelMultiples (N p : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 N).filter (p ∣ ·)

def markedSharedPrimePairs (P : Finset ℕ) (N : ℕ) : Finset (ℕ × ℕ) :=
  P.biUnion (fun p => (markedLabelMultiples N p).product (markedLabelMultiples N p))

theorem mem_markedSharedPrimePairs (P : Finset ℕ) (N a b : ℕ) :
    (a, b) ∈ markedSharedPrimePairs P N ↔
      0 < a ∧ a ≤ N ∧ 0 < b ∧ b ≤ N ∧ ∃ p ∈ P, p ∣ a ∧ p ∣ b := by
  simp only [markedSharedPrimePairs, Finset.mem_biUnion, Finset.product_eq_sprod, Finset.mem_product,
    markedLabelMultiples, Finset.mem_filter, Finset.mem_Ioc]
  aesop

theorem markedLabelMultiples_card (N p : ℕ) :
    (markedLabelMultiples N p).card = N / p :=
  Nat.Ioc_filter_dvd_card_eq_div N p

/-- Exact union bound for the ordered shared-prime label pairs. -/
theorem markedSharedPrimePairs_card_le (P : Finset ℕ) (N : ℕ) :
    (markedSharedPrimePairs P N).card ≤ ∑ p ∈ P, (N / p) ^ 2 := by
  apply Finset.card_biUnion_le.trans
  apply Finset.sum_le_sum
  intro p _
  rw [Finset.product_eq_sprod, Finset.card_product, markedLabelMultiples_card, pow_two]

/-- The reciprocal-square bound for the actual numeric pair count. -/
theorem markedSharedPrimePairs_real_card_le (P : Finset ℕ) (N : ℕ) :
    ((markedSharedPrimePairs P N).card : ℝ) ≤
      (N : ℝ) ^ 2 * ∑ p ∈ P, 1 / (p : ℝ) ^ 2 := by
  calc
    ((markedSharedPrimePairs P N).card : ℝ) ≤ ∑ p ∈ P, ((N / p : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast markedSharedPrimePairs_card_le P N
    _ ≤ ∑ p ∈ P, ((N : ℝ) / p) ^ 2 := by
      apply Finset.sum_le_sum
      intro p _
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) Nat.cast_div_le 2
    _ = (N : ℝ) ^ 2 * ∑ p ∈ P, 1 / (p : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring

theorem markedSharedPrimePairs_density_le (P : Finset ℕ) (N : ℕ) :
    ((markedSharedPrimePairs P N).card : ℝ) / (N : ℝ) ^ 2 ≤
      ∑ p ∈ P, 1 / (p : ℝ) ^ 2 := by
  by_cases hN : N = 0
  · subst N
    simp only [Nat.cast_zero, zero_pow two_ne_zero, div_zero]
    positivity
  · apply (div_le_iff₀ (sq_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hN))).mpr
    simpa only [mul_comm] using markedSharedPrimePairs_real_card_le P N

/-- The normalized count of actual numeric products sharing any marking prime
saves every fixed logarithmic power, for any growing cutoff. -/
theorem markedSharedPrimePairs_log_saving {ι : Type*} (I : Finset ι)
    (a : ι → ℝ) (ha : ∀ i ∈ I, (1 / 10 : ℝ) ≤ a i) (N : ℝ → ℕ) (A : ℝ) :
    Tendsto (fun x : ℝ => (Real.log x) ^ A *
      (((markedSharedPrimePairs (I.biUnion (fun i => markedLogPowerBand (a i) x)) (N x)).card : ℝ) /
        (N x : ℝ) ^ 2)) atTop (nhds 0) := by
  have hlimit := marked_bands_reciprocal_square_log_saving I a ha A
  apply squeeze_zero' _ _ hlimit
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    apply mul_nonneg (Real.rpow_nonneg (Real.log_nonneg hx) A)
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact mul_le_mul_of_nonneg_left (markedSharedPrimePairs_density_le _ _)
      (Real.rpow_nonneg (Real.log_nonneg hx) A)

end ArtinMatthews
