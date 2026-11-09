module

public import ArtinMatthews.CubicSieveBlockRelative


set_option backward.privateInPublic true
@[expose] public section

/-! The true top-down depth schedule controls every omitted-block product. -/

noncomputable section
namespace ArtinMatthews

open Finset
open scoped BigOperators

def cubicSieveBlockLoss (m j : ℕ) : ℝ :=
  (1 / 4 : ℝ) ^ (2 * cubicSieveOrder m j + 1)

theorem cubicSieve_half_geometric_sum (I : Finset ℕ) :
    (∑ j ∈ I, (1 / 2 : ℝ) ^ j) ≤ 2 := by
  have hsub : I ⊆ range (I.sup id + 1) :=
    fun j hj => mem_range.mpr (Nat.lt_succ_of_le (le_sup (f := id) hj))
  exact (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans
    (sum_geometric_two_le _)

theorem cubicSieve_blockLoss_sum_le (I : Finset ℕ) {m : ℕ} (hm : 1 ≤ m) :
    (∑ j ∈ I, cubicSieveBlockLoss m j) ≤ 2 * Real.exp (-(2 * (m : ℝ))) := by
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hq : (1 / 4 : ℝ) ≤ Real.exp (-1) := by
    have hlog4 : 1 ≤ Real.log 4 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      linarith only [hlog]
    rw [one_div, Real.exp_neg]
    exact inv_anti₀ (Real.exp_pos _) ((Real.le_log_iff_exp_le (by norm_num)).mp hlog4)
  have hmexp : (1 / 4 : ℝ) ^ (2 * m) ≤ Real.exp (-(2 * (m : ℝ))) := by
    calc
      _ ≤ Real.exp (-1) ^ (2 * m) := pow_le_pow_left₀ (by norm_num) hq _
      _ = _ := by rw [← Real.exp_nat_mul]; push_cast; congr 1; ring
  have hpoint (j : ℕ) :
      cubicSieveBlockLoss m j ≤ Real.exp (-(2 * (m : ℝ))) * (1 / 2 : ℝ) ^ j := by
    have hj : j ≤ j * (2 * m) := Nat.le_mul_of_pos_right _ (by omega)
    have he : 2 * cubicSieveOrder m j + 1 = 2 * m + j * (2 * m) + 1 := by
      unfold cubicSieveOrder
      ring
    have hidx : 2 * m + j ≤ 2 * cubicSieveOrder m j + 1 := by rw [he]; omega
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hidx
    calc
      cubicSieveBlockLoss m j ≤ (1 / 4 : ℝ) ^ (2 * m + j) := by
        unfold cubicSieveBlockLoss
        rw [hk, pow_add]
        exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
      _ = (1 / 4 : ℝ) ^ (2 * m) * (1 / 4 : ℝ) ^ j := pow_add _ _ _
      _ ≤ _ := mul_le_mul hmexp (pow_le_pow_left₀ (by norm_num) (by norm_num) _)
        (by positivity) (Real.exp_pos _).le
  calc
    _ ≤ ∑ j ∈ I, Real.exp (-(2 * (m : ℝ))) * (1 / 2 : ℝ) ^ j :=
      sum_le_sum (fun j _ => hpoint j)
    _ = Real.exp (-(2 * (m : ℝ))) * (∑ j ∈ I, (1 / 2 : ℝ) ^ j) := (mul_sum _ _ _).symm
    _ ≤ _ := (mul_le_mul_of_nonneg_left (cubicSieve_half_geometric_sum I)
      (Real.exp_pos _).le).trans_eq (mul_comm _ _)

theorem cubicSieve_blockProducts_le (I : Finset ℕ) (u : ℕ → ℝ) {m : ℕ} (hm : 1 ≤ m)
    {C : ℝ} (hC : 0 ≤ C) (hu₀ : ∀ j ∈ I, 0 ≤ u j)
    (hu : ∀ j ∈ I, u j ≤ 1 + C * cubicSieveBlockLoss m j) :
    (∏ j ∈ I, u j) ≤ Real.exp (2 * C) := by
  have hsum := cubicSieve_blockLoss_sum_le I hm
  have hexp : Real.exp (-(2 * (m : ℝ))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  calc
    _ ≤ ∏ j ∈ I, (1 + C * cubicSieveBlockLoss m j) := prod_le_prod₀ hu₀ hu
    _ ≤ Real.exp (∑ j ∈ I, C * cubicSieveBlockLoss m j) :=
      Real.prod_one_add_le_exp_sum I (fun j => mul_nonneg hC (by unfold cubicSieveBlockLoss; positivity))
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      rw [← mul_sum]
      exact (mul_le_mul_of_nonneg_left (hsum.trans
        (mul_le_of_le_one_right (by norm_num) hexp)) hC).trans_eq (mul_comm _ _)

theorem cubicSieve_blockProducts_tangent_le (I : Finset ℕ) (u v : ℕ → ℝ) {m : ℕ}
    (hm : 1 ≤ m) {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hu₀ : ∀ j ∈ I, 0 ≤ u j) (hu : ∀ j ∈ I, u j ≤ 1 + C * cubicSieveBlockLoss m j)
    (hv : ∀ j ∈ I, |v j| ≤ 2 * C * L * (1 / 2 : ℝ) ^ j) :
    |cubicSieveProdTangent I u v| ≤ 4 * C * Real.exp (2 * C) * L := by
  unfold cubicSieveProdTangent
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ j ∈ I, Real.exp (2 * C) * (2 * C * L * (1 / 2 : ℝ) ^ j) := by
      apply sum_le_sum
      intro j hj
      have hpos : 0 ≤ ∏ i ∈ I.erase j, u i := prod_nonneg (fun i hi => hu₀ i (mem_of_mem_erase hi))
      rw [abs_mul, abs_of_nonneg hpos]
      exact mul_le_mul (cubicSieve_blockProducts_le _ u hm hC
        (fun i hi => hu₀ i (mem_of_mem_erase hi)) (fun i hi => hu i (mem_of_mem_erase hi)))
        (hv j hj) (abs_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (2 * C) * (2 * C * L) * ∑ j ∈ I, (1 / 2 : ℝ) ^ j := by
      simp only [← mul_assoc, ← mul_sum]
    _ ≤ _ := (mul_le_mul_of_nonneg_left (cubicSieve_half_geometric_sum I) (by positivity)).trans_eq
      (by ring)

end ArtinMatthews
