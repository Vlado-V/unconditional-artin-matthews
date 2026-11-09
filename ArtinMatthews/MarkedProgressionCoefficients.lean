module

public import ArtinMatthews.MarkedProgressionTruncation
public import Mathlib.Data.Nat.Choose.Bounds


set_option backward.privateInPublic true
@[expose] public section

/-! Explicit coefficient mass and level controls for finite Bonferroni
polynomials. No asymptotic bound is assumed at this finite stage. -/

namespace ArtinMatthews

open scoped BigOperators

/-- The absolute mass of one homogeneous level is bounded by the number of
ordered selections, including the empty level. -/
theorem marked_homogeneous_coefficient_mass_le (P : Finset ℕ) (k : ℕ)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (∑ _T ∈ P.powersetCard k, |(-1 : ℝ) ^ k * θ ^ k|) ≤ (P.card : ℝ) ^ k := by
  calc
    _ ≤ ∑ _T ∈ P.powersetCard k, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro T _
      simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_nonneg hθ0]
      exact pow_le_one₀ hθ0 hθ1
    _ = (P.card.choose k : ℝ) := by simp [Finset.card_powersetCard]
    _ ≤ (P.card : ℝ) ^ k := by exact_mod_cast Nat.choose_le_pow P.card k

/-- The whole truncation has explicitly controlled coefficient mass. -/
theorem marked_truncation_coefficient_mass_le (P : Finset ℕ) (k : ℕ)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (∑ j ∈ Finset.range (k + 1), ∑ _T ∈ P.powersetCard j,
      |(-1 : ℝ) ^ j * θ ^ j|) ≤ (k + 1 : ℕ) * (max 1 (P.card : ℝ)) ^ k := by
  calc
    _ ≤ ∑ j ∈ Finset.range (k + 1), (P.card : ℝ) ^ j :=
      Finset.sum_le_sum (fun j _ => marked_homogeneous_coefficient_mass_le P j hθ0 hθ1)
    _ ≤ ∑ _j ∈ Finset.range (k + 1), (max 1 (P.card : ℝ)) ^ k := by
      apply Finset.sum_le_sum
      intro j hj
      exact (pow_le_pow_left₀ (Nat.cast_nonneg _) (le_max_right _ _) j).trans
        (pow_le_pow_right₀ (le_max_left _ _) (by simpa using Finset.mem_range.mp hj))
    _ = _ := by simp

/-- A selected union at residual degree at most `k` has the expected
level bound; coincidences in the selected set are automatically retained. -/
theorem marked_selected_divisor_level (P S : Finset ℕ) {z k : ℕ}
    (hz : 1 ≤ z) (hP : ∀ p ∈ P, p ≤ z) (hS : S ⊆ P)
    {j : ℕ} (hj : j ≤ k) {T : Finset ℕ} (hT : T ∈ (P \ S).powersetCard j) :
    (∏ p ∈ S ∪ T, p) ≤ z ^ (S.card + k) := by
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hT
  calc
    _ ≤ ∏ _p ∈ S ∪ T, z := by
      apply Finset.prod_le_prod
      intro p hp
      exact hP p (Finset.mem_union.mp hp |>.elim (fun h => hS h)
        (fun h => (Finset.mem_sdiff.mp (hsub h)).1))
    _ = z ^ (S ∪ T).card := by simp
    _ ≤ z ^ (S.card + k) := by
      apply Nat.pow_le_pow_right hz
      exact (Finset.card_union_le S T).trans (by omega)

end ArtinMatthews
