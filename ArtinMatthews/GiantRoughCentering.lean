module

public import ArtinMatthews.GiantRoughSieve


set_option backward.privateInPublic true
@[expose] public section

/-! Exact cancellation of the two positive rough-sieve main terms. -/

namespace ArtinMatthews

open MeasureTheory
open scoped BigOperators

theorem markedRoughPredecessorSum_centered (F H : ℕ → ℝ) (C : ℝ)
    (Φ : ℝ → ℝ) (T x γ : ℝ) :
    markedRoughPredecessorSum (fun u => (F u - C) * H u) Φ T x γ =
      markedRoughPredecessorSum (fun u => F u * H u) Φ T x γ -
        C * markedRoughPredecessorSum H Φ T x γ := by
  classical
  unfold markedRoughPredecessorSum
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem marked_centered_rough_sieve_bound (F H : ℕ → ℝ) (C M : ℝ)
    (Φ : ℝ → ℝ) (T x γ c : ℝ) (m : ℕ)
    (hx : 1 ≤ x) (hΦ : ∀ t, 0 ≤ Φ t) (hF : ∀ u, 0 ≤ F u) (hH : ∀ u, 0 ≤ H u)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hcut : 2 ≤ ⌊x ^ γ⌋₊) (hm : 20000 ≤ m)
    (hlevel : γ * ((12 * (m + 1) : ℕ) : ℝ) ≤ c) :
    |markedRoughPredecessorSum (fun u => (F u - C) * H u) Φ T x γ| ≤
      2 * C * (x * (∫ t in Set.Ioc 0 T, Φ t) * M) *
        markedSieveEulerProduct (x ^ γ) * Real.exp (-(m : ℝ) / 2) +
      markedProgressionDiscrepancy (fun u => F u * H u) (C * M) Φ T x ⌊x ^ c⌋₊ +
      C * markedProgressionDiscrepancy H M Φ T x ⌊x ^ c⌋₊ := by
  let A := markedRoughPredecessorSum (fun u => F u * H u) Φ T x γ
  let B := markedRoughPredecessorSum H Φ T x γ
  let X := (x * (∫ t in Set.Ioc 0 T, Φ t) * M) * markedSieveEulerProduct (x ^ γ)
  have h₀ := marked_rough_sieve_progression_bridge H M Φ T x γ c m hx hΦ hH hM hcut hm hlevel
  have h₁ := marked_rough_sieve_progression_bridge (fun u => F u * H u) (C * M)
    Φ T x γ c m hx hΦ (fun u => mul_nonneg (hF u) (hH u)) (mul_nonneg hC hM) hcut hm hlevel
  have hX : (x * (∫ t in Set.Ioc 0 T, Φ t) * (C * M)) *
      markedSieveEulerProduct (x ^ γ) = C * X := by dsimp [X]; ring
  rw [hX] at h₁
  have htri : |A - C * B| ≤ |A - C * X| + C * |B - X| := by
    calc
      _ = |(A - C * X) - C * (B - X)| := by congr 1; ring
      _ ≤ |A - C * X| + |C * (B - X)| := abs_sub _ _
      _ = _ := by rw [abs_mul, abs_of_nonneg hC]
  rw [markedRoughPredecessorSum_centered]
  apply htri.trans
  calc
    _ ≤ (C * X * Real.exp (-(m : ℝ) / 2) +
        markedProgressionDiscrepancy (fun u => F u * H u) (C * M) Φ T x ⌊x ^ c⌋₊) +
        C * (X * Real.exp (-(m : ℝ) / 2) + markedProgressionDiscrepancy H M Φ T x ⌊x ^ c⌋₊) :=
      add_le_add h₁ (mul_le_mul_of_nonneg_left h₀ hC)
    _ = _ := by dsimp [X]; ring

end ArtinMatthews
