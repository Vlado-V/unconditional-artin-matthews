module

public import ArtinMatthews.MarkedProgressionSelected
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset


set_option backward.privateInPublic true
@[expose] public section

/-! The actual reciprocal coprimality loss of a truncated selected marking
expansion. Every retained divisor has at most `S.card + k` prime factors,
each at least `y`; the remaining reciprocal coefficient mass is bounded
by the full positive elementary product, uniformly in the depth `k`. -/

namespace ArtinMatthews

open OAI.Erdos970.NumberTheoryLean
open scoped BigOperators

/-- A partial sum of nonnegative elementary layers is bounded by its full
Euler product, and hence by the exponential of the available mass. -/
theorem marked_elementary_partial_sum_le_exp (Q : Finset ℕ) (g : ℕ → ℝ)
    (k : ℕ) (hg : ∀ p ∈ Q, 0 ≤ g p) {V : ℝ} (hmass : ∑ p ∈ Q, g p ≤ V) :
    (∑ j ∈ Finset.range (k + 1), BonferroniDensity.elementarySum Q g j) ≤ Real.exp V := by
  classical
  have hpartial :
      (∑ j ∈ Finset.range (k + 1), BonferroniDensity.elementarySum Q g j) ≤
        ∑ j ∈ Finset.range (Q.card + 1), BonferroniDensity.elementarySum Q g j := by
    by_cases hk : k ≤ Q.card
    · apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (Nat.add_le_add_right hk 1))
      intro j _ _
      exact BonferroniDensity.elementarySum_nonneg Q g hg j
    · have hcard : Q.card ≤ k := by omega
      have heq :
          (∑ j ∈ Finset.range (Q.card + 1), BonferroniDensity.elementarySum Q g j) =
            ∑ j ∈ Finset.range (k + 1), BonferroniDensity.elementarySum Q g j := by
        apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hcard 1))
        intro j _ hj
        have hlarge : Q.card < j := by
          simp only [Finset.mem_range] at hj
          omega
        simp only [BonferroniDensity.elementarySum,
          Finset.powersetCard_eq_empty.mpr hlarge, Finset.sum_empty]
      exact heq.ge
  calc
    _ ≤ ∑ j ∈ Finset.range (Q.card + 1), BonferroniDensity.elementarySum Q g j := hpartial
    _ = ∑ T ∈ Q.powerset, ∏ p ∈ T, g p := by
      simpa only [BonferroniDensity.elementarySum] using
        (Finset.sum_powerset Q (fun T => ∏ p ∈ T, g p)).symm
    _ = ∏ p ∈ Q, (1 + g p) := (Finset.prod_one_add Q).symm
    _ ≤ ∏ p ∈ Q, Real.exp (g p) := by
      apply Finset.prod_le_prod₀
      · intro p hp
        linarith [hg p hp]
      · intro p _
        simpa only [add_comm] using Real.add_one_le_exp (g p)
    _ = Real.exp (∑ p ∈ Q, g p) := by rw [Real.exp_sum]
    _ ≤ Real.exp V := Real.exp_le_exp.mpr hmass

/-- Reciprocal elementary mass with arbitrary nonnegative prime weights,
including different damping parameters on disjoint bands. -/
theorem marked_weighted_elementary_partial_sum_le_exp (Q : Finset ℕ)
    (θ : ℕ → ℝ) (k : ℕ) (hθ : ∀ p ∈ Q, 0 ≤ θ p)
    {V : ℝ} (hmass : ∑ p ∈ Q, θ p / (p : ℝ) ≤ V) :
    (∑ j ∈ Finset.range (k + 1),
      BonferroniDensity.elementarySum Q (fun p => θ p / (p : ℝ)) j) ≤ Real.exp V :=
  marked_elementary_partial_sum_le_exp Q (fun p => θ p / (p : ℝ)) k
    (fun p hp => div_nonneg (hθ p hp) (Nat.cast_nonneg p)) hmass

/-- Prime reciprocal mass of a retained represented divisor. -/
theorem marked_union_prime_reciprocal_le (P S T : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hS : S ⊆ P) (hT : T ⊆ P \ S)
    (k : ℕ) (hTk : T.card ≤ k) {y : ℝ} (hy : 0 < y)
    (hmin : ∀ p ∈ P, y ≤ (p : ℝ)) :
    (∑ p ∈ (∏ q ∈ S ∪ T, q : ℕ).primeFactors, 1 / (p : ℝ)) ≤
      ((S.card + k : ℕ) : ℝ) / y := by
  classical
  have hU : S ∪ T ⊆ P := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact hS hp
    · exact (Finset.mem_sdiff.mp (hT hp)).1
  rw [Nat.primeFactors_prod (fun p hp => hP p (hU hp))]
  have hcard : (S ∪ T).card ≤ S.card + k :=
    (Finset.card_union_le S T).trans (Nat.add_le_add_left hTk S.card)
  calc
    _ ≤ ∑ _p ∈ S ∪ T, 1 / y := by
      apply Finset.sum_le_sum
      intro p hp
      exact one_div_le_one_div_of_le hy (hmin p (hU hp))
    _ = ((S ∪ T).card : ℝ) / y := by simp [div_eq_mul_inv]
    _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast hcard) hy.le

/-- Summed reciprocal mass of all retained selected layers. -/
theorem marked_selected_partial_reciprocal_mass (P S : Finset ℕ) (k : ℕ) (θ : ℝ) :
    (∑ j ∈ Finset.range (k + 1), ∑ T ∈ (P \ S).powersetCard j,
      θ ^ j / (∏ p ∈ S ∪ T, p : ℕ)) =
      (1 / (∏ p ∈ S, p : ℕ)) *
        ∑ j ∈ Finset.range (k + 1),
          BonferroniDensity.elementarySum (P \ S) (fun p => θ / (p : ℝ)) j := by
  simp_rw [marked_selected_reciprocal_mass]
  rw [Finset.mul_sum]

/-- Exact selected reciprocal coefficient mass is bounded uniformly in the
truncation depth. Nonnegativity of `θ` suffices; `θ ≤ 1` is not needed. -/
theorem marked_selected_partial_reciprocal_mass_le_exp (P S : Finset ℕ)
    (k : ℕ) {θ V : ℝ} (hθ : 0 ≤ θ)
    (hmass : ∑ p ∈ P \ S, θ / (p : ℝ) ≤ V) :
    (∑ j ∈ Finset.range (k + 1), ∑ T ∈ (P \ S).powersetCard j,
      θ ^ j / (∏ p ∈ S ∪ T, p : ℕ)) ≤
      (1 / (∏ p ∈ S, p : ℕ)) * Real.exp V := by
  rw [marked_selected_partial_reciprocal_mass]
  exact mul_le_mul_of_nonneg_left
    (marked_elementary_partial_sum_le_exp (P \ S) (fun p => θ / (p : ℝ)) k
      (fun p _ => div_nonneg hθ (Nat.cast_nonneg p)) hmass) (by positivity)

/-- Full truncated coprimality coefficient loss, with its actual represented
reciprocal factor and the depth-uniform exponential constant retained. -/
theorem marked_selected_truncated_local_loss_le (P S : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hS : S ⊆ P) (k : ℕ)
    {y θ V : ℝ} (hy : 0 < y) (hmin : ∀ p ∈ P, y ≤ (p : ℝ))
    (hθ : 0 ≤ θ) (hmass : ∑ p ∈ P \ S, θ / (p : ℝ) ≤ V) :
    (∑ j ∈ Finset.range (k + 1), ∑ T ∈ (P \ S).powersetCard j,
      (θ ^ j / (∏ p ∈ S ∪ T, p : ℕ)) *
        ∑ q ∈ (∏ p ∈ S ∪ T, p : ℕ).primeFactors, 1 / (q : ℝ)) ≤
      (((S.card + k : ℕ) : ℝ) / y) *
        (1 / (∏ p ∈ S, p : ℕ)) * Real.exp V := by
  classical
  let A : ℝ := ((S.card + k : ℕ) : ℝ) / y
  have hA : 0 ≤ A := by dsimp [A]; positivity
  calc
    _ ≤ ∑ j ∈ Finset.range (k + 1), ∑ T ∈ (P \ S).powersetCard j,
        (θ ^ j / (∏ p ∈ S ∪ T, p : ℕ)) * A := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro T hT
      obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hT
      have hTk : T.card ≤ k := by
        rw [hcard]
        exact Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      exact mul_le_mul_of_nonneg_left
        (marked_union_prime_reciprocal_le P S T hP hS hsub k hTk hy hmin)
        (div_nonneg (pow_nonneg hθ j) (Nat.cast_nonneg _))
    _ = A * (∑ j ∈ Finset.range (k + 1), ∑ T ∈ (P \ S).powersetCard j,
        θ ^ j / (∏ p ∈ S ∪ T, p : ℕ)) := by
      simp_rw [← Finset.sum_mul]
      rw [mul_comm]
    _ ≤ A * ((1 / (∏ p ∈ S, p : ℕ)) * Real.exp V) :=
      mul_le_mul_of_nonneg_left
        (marked_selected_partial_reciprocal_mass_le_exp P S k hθ hmass) hA
    _ = _ := by rw [mul_assoc]

end ArtinMatthews
