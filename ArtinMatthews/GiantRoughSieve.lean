module

public import ArtinMatthews.MarkedSieveProgressionBridge
public import ArtinMatthews.MarkedTypeIICoefficients


set_option backward.privateInPublic true
@[expose] public section

/-! The proved two-sided fundamental sieve for actual rough predecessor sums. -/

namespace ArtinMatthews

open MeasureTheory OAI.Erdos970.NumberTheoryLean Classical
open scoped BigOperators

theorem marked_survives_eq_rough_indicator (y : ℝ) (hy : 0 ≤ y) (u : ℕ) :
    BonferroniBlocks.survives (Nat.primesLE ⌊y⌋₊) (fun p => p ∣ u + 1) =
      if MarkedRoughAbove y (u + 1) then (1 : ℝ) else 0 := by
  classical
  have heq : (∀ p ∈ Nat.primesLE ⌊y⌋₊, ¬p ∣ u + 1) ↔ MarkedRoughAbove y (u + 1) := by
    constructor
    · intro h p hp hpu
      by_contra hn
      have hle : (p : ℝ) ≤ y := le_of_not_gt hn
      exact h p (Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff hy).mpr hle, hp⟩) hpu
    · intro h p hp hpu
      have hle : (p : ℝ) ≤ y := (Nat.le_floor_iff hy).mp (Nat.le_of_mem_primesLE hp)
      exact (not_lt_of_ge hle) (h p (Nat.prime_of_mem_primesLE hp) hpu)
  unfold BonferroniBlocks.survives
  simp only [heq]

noncomputable def markedRoughPredecessorSum (H : ℕ → ℝ) (Φ : ℝ → ℝ)
    (T x γ : ℝ) : ℝ := by
  classical
  exact ∑ u ∈ (Finset.Icc 0 ⌊T * x⌋₊).filter (fun u => MarkedRoughAbove (x ^ γ) (u + 1)),
    Φ ((u : ℝ) / x) * H u

/-- The actual rough sum is controlled on both sides of its Euler main
term. The discrepancy on the right is the concrete summed progression error. -/
theorem marked_rough_sieve_progression_bridge (H : ℕ → ℝ) (M : ℝ)
    (Φ : ℝ → ℝ) (T x γ c : ℝ) (m : ℕ)
    (hx : 1 ≤ x) (hΦ : ∀ t, 0 ≤ Φ t) (hH : ∀ u, 0 ≤ H u) (hM : 0 ≤ M)
    (hcut : 2 ≤ ⌊x ^ γ⌋₊) (hm : 20000 ≤ m)
    (hlevel : γ * ((12 * (m + 1) : ℕ) : ℝ) ≤ c) :
    |markedRoughPredecessorSum H Φ T x γ -
        (x * (∫ t in Set.Ioc 0 T, Φ t) * M) * markedSieveEulerProduct (x ^ γ)| ≤
      (x * (∫ t in Set.Ioc 0 T, Φ t) * M) * markedSieveEulerProduct (x ^ γ) *
        Real.exp (-(m : ℝ) / 2) +
      markedProgressionDiscrepancy H M Φ T x ⌊x ^ c⌋₊ := by
  classical
  let U := Finset.Icc 0 ⌊T * x⌋₊
  let w (u : ℕ) := Φ ((u : ℝ) / x) * H u
  let X := x * (∫ t in Set.Ioc 0 T, Φ t) * M
  let P := Nat.primesLE ⌊x ^ γ⌋₊
  have hP : ∀ p ∈ P, p.Prime := fun _ hp => Nat.prime_of_mem_primesLE hp
  have hX : 0 ≤ X := mul_nonneg (mul_nonneg (le_trans zero_le_one hx) (integral_nonneg hΦ)) hM
  have h := FundamentalBlockEstimate.finite_fundamental_integer_level U w
    (fun u _ => mul_nonneg (hΦ _) (hH u)) (fun p u => p ∣ u + 1)
    ⌊x ^ γ⌋₊ m P X (fun p => 1 / (p : ℝ)) hcut hm hX hP
    (fun _ hp => Nat.le_of_mem_primesLE hp) (fun _ _ => by positivity)
    (fun p _ => div_le_div_of_nonneg_right (by norm_num) (Nat.cast_nonneg p))
    (fun _ => le_rfl)
  have hrem : (∑ d ∈ FundamentalBlockEstimate.levelDivisors P (⌊x ^ γ⌋₊ ^ (12 * (m + 1))),
      |FundamentalBlockEstimate.integerRemainder U w (fun p u => p ∣ u + 1) X
        (fun p => 1 / (p : ℝ)) d|) =
      ∑ d ∈ FundamentalBlockEstimate.levelDivisors P (⌊x ^ γ⌋₊ ^ (12 * (m + 1))),
        |predecessorProgressionRemainder U w X d| := by
    apply Finset.sum_congr rfl
    intro d hd
    have hpd : d ∣ ∏ p ∈ P, p := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
    rw [predecessor_integerRemainder U w X
      ((IntervalBoundingSieve.squarefree_primeSet_product P hP).squarefree_of_dvd hpd)]
  rw [hrem] at h
  have heq : (∑ u ∈ U, w u * BonferroniBlocks.survives P (fun p => p ∣ u + 1)) =
      markedRoughPredecessorSum H Φ T x γ := by
    simp only [P, marked_survives_eq_rough_indicator _ (Real.rpow_nonneg (le_trans zero_le_one hx) _)]
    simp only [markedRoughPredecessorSum, Finset.sum_filter, mul_ite, mul_one, mul_zero, U, w]
  rw [heq] at h
  exact h.trans (add_le_add le_rfl
    (marked_sieve_remainders_le_discrepancy H M Φ T x γ c m hx hlevel))

end ArtinMatthews
