module

public import ArtinMatthews.Definitions
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! The convergent reciprocal kernel in the small-index splitting estimate. -/

namespace ArtinMatthews

/-- Exact finite telescoping identity, with a positive starting denominator. -/
theorem sum_reciprocal_successor_product (Y k : ℕ) (hY : 0 < Y) :
    (∑ i ∈ Finset.range k, 1 / (((Y : ℝ) + i + 1) * ((Y : ℝ) + i))) =
      1 / (Y : ℝ) - 1 / ((Y : ℝ) + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    have hY0 : (Y : ℝ) ≠ 0 := by positivity
    have hYk : (Y : ℝ) + k ≠ 0 := by positivity
    have hYk1 : (Y : ℝ) + k + 1 ≠ 0 := by positivity
    field_simp
    ring

/-- Every finite subset of the tail has total kernel mass at most `1/Y`. -/
theorem sum_reciprocal_tail_le (P : Finset ℕ) (Y : ℕ) (hY : 0 < Y)
    (hP : ∀ p ∈ P, Y < p) :
    (∑ p ∈ P, 1 / ((p : ℝ) * ((p : ℝ) - 1))) ≤ 1 / (Y : ℝ) := by
  classical
  let Q := P.image (fun p => p - Y - 1)
  let k := Q.sup id + 1
  have hQ : Q ⊆ Finset.range k := by
    intro i hi
    apply Finset.mem_range.mpr
    have : i ≤ Q.sup id := Finset.le_sup (f := id) hi
    dsimp [k]
    omega
  have hsum : (∑ p ∈ P, 1 / ((p : ℝ) * ((p : ℝ) - 1))) =
      ∑ i ∈ Q, 1 / (((Y : ℝ) + i + 1) * ((Y : ℝ) + i)) := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro p hp
      have hy : Y < p := hP p hp
      have hid : Y + (p - Y - 1) + 1 = p := by omega
      have hidR : (Y : ℝ) + (p - Y - 1 : ℕ) + 1 = p := by exact_mod_cast hid
      congr 2 <;> linarith
    · intro p hp q hq heq
      have := hP p hp
      have := hP q hq
      dsimp at heq
      omega
  rw [hsum]
  calc
    (∑ i ∈ Q, 1 / (((Y : ℝ) + i + 1) * ((Y : ℝ) + i))) ≤
        ∑ i ∈ Finset.range k, 1 / (((Y : ℝ) + i + 1) * ((Y : ℝ) + i)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hQ
      intro i _ _
      positivity
    _ = 1 / (Y : ℝ) - 1 / ((Y : ℝ) + k) := sum_reciprocal_successor_product Y k hY
    _ ≤ 1 / (Y : ℝ) := sub_le_self _ (by positivity)

end ArtinMatthews
