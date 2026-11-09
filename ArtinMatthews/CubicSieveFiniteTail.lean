module

public import ArtinMatthews.CubicSieveBlockProducts


set_option backward.privateInPublic true
@[expose] public section

/-! Finite tail estimates for the actual total-degree truncation. -/

noncomputable section
namespace ArtinMatthews

open Finset
open scoped BigOperators

theorem cubicSieve_quarter_geometric_tail (I : Finset ℕ) (k : ℕ)
    (hI : ∀ j ∈ I, k ≤ j) :
    (∑ j ∈ I, (1 / 4 : ℝ) ^ j) ≤ 2 * (1 / 4 : ℝ) ^ k := by
  have hinj : Set.InjOn (fun j => j - k) (I : Set ℕ) := by
    intro a ha b hb he
    change a - k = b - k at he
    have hka := hI a ha
    have hkb := hI b hb
    omega
  calc
    _ = (1 / 4 : ℝ) ^ k * ∑ j ∈ I.image (fun j => j - k), (1 / 4 : ℝ) ^ j := by
      rw [mul_sum, sum_image hinj]
      apply sum_congr rfl
      intro j hj
      rw [← pow_add, Nat.add_sub_of_le (hI j hj)]
    _ ≤ (1 / 4 : ℝ) ^ k * ∑ j ∈ I.image (fun j => j - k), (1 / 2 : ℝ) ^ j := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact sum_le_sum (fun j _ => pow_le_pow_left₀ (by norm_num) (by norm_num) j)
    _ ≤ _ := (mul_le_mul_of_nonneg_left (cubicSieve_half_geometric_sum _) (by positivity)).trans_eq
      (mul_comm _ _)

theorem cubicSieve_truncation_split (K k : ℕ) (f : ℕ → ℝ)
    (hzero : ∀ j, K < j → f j = 0) :
    (∑ j ∈ range (k + 1), f j) + (∑ j ∈ (range (K + 1)).filter (fun j => k < j), f j) =
      ∑ j ∈ range (K + 1), f j := by
  let I := (range (K + 1)).filter (fun j => j ≤ k)
  have hsub : I ⊆ range (k + 1) := fun j hj =>
    mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp hj).2)
  have he : (∑ j ∈ range (k + 1), f j) = ∑ j ∈ I, f j := by
    symm
    apply sum_subset hsub
    intro j hj hjI
    have hkj : j ≤ k := Nat.le_of_lt_succ (mem_range.mp hj)
    have hlarge : K < j := by
      by_contra! h
      exact hjI (mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le h), hkj⟩)
    exact hzero j hlarge
  rw [he]
  simpa only [I, not_le] using
    sum_filter_add_sum_filter_not (range (K + 1)) (fun j => j ≤ k) f

theorem cubicSieve_truncation_tail_abs_le (K k : ℕ) (f : ℕ → ℝ) {B : ℝ}
    (hB : 0 ≤ B) (hzero : ∀ j, K < j → f j = 0)
    (hbound : ∀ j, |f j| ≤ B * (1 / 4 : ℝ) ^ j) :
    |(∑ j ∈ range (k + 1), f j) - (∑ j ∈ range (K + 1), f j)| ≤
      2 * B * (1 / 4 : ℝ) ^ k := by
  have he := cubicSieve_truncation_split K k f hzero
  have hdiff : (∑ j ∈ range (k + 1), f j) - (∑ j ∈ range (K + 1), f j) =
      -(∑ j ∈ (range (K + 1)).filter (fun j => k < j), f j) := by linarith only [he]
  rw [hdiff, abs_neg]
  calc
    _ ≤ ∑ j ∈ (range (K + 1)).filter (fun j => k < j), |f j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ (range (K + 1)).filter (fun j => k < j), B * (1 / 4 : ℝ) ^ j :=
      sum_le_sum (fun j _ => hbound j)
    _ = B * ∑ j ∈ (range (K + 1)).filter (fun j => k < j), (1 / 4 : ℝ) ^ j := (mul_sum _ _ _).symm
    _ ≤ _ := (mul_le_mul_of_nonneg_left
      (cubicSieve_quarter_geometric_tail _ k (fun j hj => (mem_filter.mp hj).2.le)) hB).trans_eq
      (by ring)

end ArtinMatthews
