module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.MeanInequalities


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite weighted-square AM-GM bounds for total-height energy. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem sourceFinite_card_mul_geometricMean_le_sum (z : ι → ℝ)
    (hz : ∀ i, 0 ≤ z i) :
    (Fintype.card ι : ℝ) * (∏ i, z i) ^ (1 / (Fintype.card ι : ℝ)) ≤ ∑ i, z i := by
  have hr : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hm := Real.geom_mean_le_arith_mean Finset.univ (fun _ : ι => (1 : ℝ)) z
    (fun _ _ => zero_le_one) (by simpa using hr) (fun i _ => hz i)
  have hm' : (∏ i, z i) ^ (Fintype.card ι : ℝ)⁻¹ ≤ (∑ i, z i) / (Fintype.card ι : ℝ) := by
    simpa only [Real.rpow_one, one_mul, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one] using hm
  simpa only [one_div, mul_comm] using (le_div_iff₀ hr).mp hm'

theorem sourceFinite_weighted_square_amgm (y q : ι → ℝ) (N0 : ℝ)
    (hy : ∀ i, 0 < y i) (hq : ∀ i, 0 ≤ q i) (hN0 : 0 < N0)
    (hprod : N0 ≤ ∏ i, q i ^ 2) :
    (Fintype.card ι : ℝ) * ((∏ i, y i ^ 2) * N0) ^ (1 / (Fintype.card ι : ℝ)) ≤
      ∑ i, (y i * q i) ^ 2 := by
  have hr : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hyprod : 0 ≤ ∏ i, y i ^ 2 := Finset.prod_nonneg (fun i _ => sq_nonneg (y i))
  have hA : 0 ≤ (∏ i, y i ^ 2) * N0 := mul_nonneg hyprod hN0.le
  have hp : (∏ i, y i ^ 2) * N0 ≤ ∏ i, (y i * q i) ^ 2 := by
    calc
      _ ≤ (∏ i, y i ^ 2) * (∏ i, q i ^ 2) := mul_le_mul_of_nonneg_left hprod hyprod
      _ = _ := by simp only [mul_pow, Finset.prod_mul_distrib]
  have hroot := Real.rpow_le_rpow hA hp (one_div_pos.mpr hr).le
  exact (mul_le_mul_of_nonneg_left hroot hr.le).trans
    (sourceFinite_card_mul_geometricMean_le_sum (fun i => (y i * q i) ^ 2)
      (fun i => pow_nonneg (mul_nonneg (hy i).le (hq i)) 2))

theorem sourceFinite_weighted_square_amgm_pow (y q : ι → ℝ) (N0 : ℝ)
    (hy : ∀ i, 0 < y i) (hq : ∀ i, 0 ≤ q i) (hN0 : 0 < N0)
    (hprod : N0 ≤ ∏ i, q i ^ 2) :
    (Fintype.card ι : ℝ) ^ Fintype.card ι * ((∏ i, y i ^ 2) * N0) ≤
      (∑ i, (y i * q i) ^ 2) ^ Fintype.card ι := by
  have hr : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hA : 0 ≤ (∏ i, y i ^ 2) * N0 :=
    mul_nonneg (Finset.prod_nonneg (fun i _ => sq_nonneg (y i))) hN0.le
  have hmean : ((∏ i, y i ^ 2) * N0) ^ (Fintype.card ι : ℝ)⁻¹ ≤
      (∑ i, (y i * q i) ^ 2) / (Fintype.card ι : ℝ) := by
    apply (le_div_iff₀ hr).mpr
    simpa only [one_div, mul_comm] using sourceFinite_weighted_square_amgm y q N0 hy hq hN0 hprod
  have hp := pow_le_pow_left₀ (Real.rpow_nonneg hA _) hmean (Fintype.card ι)
  rw [Real.rpow_inv_natCast_pow hA (Nat.ne_of_gt Fintype.card_pos)] at hp
  calc
    _ ≤ (Fintype.card ι : ℝ) ^ Fintype.card ι *
        ((∑ i, (y i * q i) ^ 2) / (Fintype.card ι : ℝ)) ^ Fintype.card ι :=
      mul_le_mul_of_nonneg_left hp (pow_nonneg hr.le _)
    _ = _ := by
      rw [div_pow]
      field_simp

theorem sourceFinite_weighted_abs_square_amgm (y ξ : ι → ℝ) (N0 : ℝ)
    (hy : ∀ i, 0 < y i) (hN0 : 0 < N0) (hprod : N0 ≤ ∏ i, |ξ i| ^ 2) :
    (Fintype.card ι : ℝ) * ((∏ i, y i ^ 2) * N0) ^ (1 / (Fintype.card ι : ℝ)) ≤
      ∑ i, (y i * |ξ i|) ^ 2 :=
  sourceFinite_weighted_square_amgm y (fun i => |ξ i|) N0 hy (fun i => abs_nonneg (ξ i)) hN0 hprod

end
end ArtinMatthews
