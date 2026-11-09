module

public import ArtinMatthews.QuadraticB2PoissonCutoff


set_option backward.privateInPublic true
@[expose] public section

/-! An explicit tail line for every cutoff in the B3 range. -/
namespace ArtinMatthews.QuadraticScale
noncomputable section

def quadraticB3TailLine (δ : ℝ) : ℝ := 2 + 3 / δ

theorem quadraticB3TailLine_ge_two {δ : ℝ} (hδ : 0 < δ) :
    2 ≤ quadraticB3TailLine δ := by
  unfold quadraticB3TailLine
  exact le_add_of_nonneg_right (by positivity)

theorem quadraticB3_cutoff_range {M P K δ : ℝ}
    (hM : 1 ≤ M) (hP : 1 ≤ P) (hδ : 0 < δ)
    (hlower : P ^ 2 / M * (M * P) ^ δ ≤ K)
    (hupper : K ≤ M * (M * P) ^ (-δ)) :
    0 < K ∧ K ≤ M ∧ P ^ 2 / (M * K) ≤ (M * P) ^ (-δ) := by
  have hM0 := zero_lt_one.trans_le hM
  have hP0 := zero_lt_one.trans_le hP
  have hT : 1 ≤ M * P := one_le_mul_of_one_le_of_one_le hM hP
  have hT0 := zero_lt_one.trans_le hT
  have hU0 : 0 < (M * P) ^ δ := Real.rpow_pos_of_pos hT0 δ
  have hK0 : 0 < K := (mul_pos (div_pos (sq_pos_of_pos hP0) hM0) hU0).trans_le hlower
  have hKM : K ≤ M := hupper.trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (Real.rpow_le_one_of_one_le_of_nonpos hT (neg_nonpos.mpr hδ.le)) hM0.le)
  refine ⟨hK0, hKM, ?_⟩
  rw [Real.rpow_neg hT0.le, inv_eq_one_div]
  apply (le_div_iff₀ hU0).mpr
  calc
    P ^ 2 / (M * K) * (M * P) ^ δ = (P ^ 2 / M * (M * P) ^ δ) / K := by ring
    _ ≤ 1 := (div_le_one hK0).mpr hlower

theorem quadraticB3_tail_ratio_bound {M P K δ : ℝ}
    (hM : 1 ≤ M) (hP : 1 ≤ P) (hδ : 0 < δ)
    (hlower : P ^ 2 / M * (M * P) ^ δ ≤ K)
    (hupper : K ≤ M * (M * P) ^ (-δ)) :
    M / P * K ^ 2 * (P ^ 2 / (M * K)) ^ quadraticB3TailLine δ ≤ M / P := by
  obtain ⟨hK0, hKM, hratio⟩ := quadraticB3_cutoff_range hM hP hδ hlower hupper
  have hM0 := zero_lt_one.trans_le hM
  have hP0 := zero_lt_one.trans_le hP
  have hT : 1 ≤ M * P := one_le_mul_of_one_le_of_one_le hM hP
  have hT0 := zero_lt_one.trans_le hT
  have hline : 0 ≤ quadraticB3TailLine δ :=
    (by norm_num : (0 : ℝ) ≤ 2).trans (quadraticB3TailLine_ge_two hδ)
  have hbudget : 2 ≤ δ * quadraticB3TailLine δ := by
    unfold quadraticB3TailLine
    have hcancel : δ * (3 / δ) = 3 := by field_simp
    nlinarith
  have hKsq : K ^ 2 ≤ (M * P) ^ 2 :=
    pow_le_pow_left₀ hK0.le (hKM.trans (le_mul_of_one_le_right hM0.le hP)) 2
  have hpower : (P ^ 2 / (M * K)) ^ quadraticB3TailLine δ ≤
      (M * P) ^ (-δ * quadraticB3TailLine δ) := by
    calc
      _ ≤ ((M * P) ^ (-δ)) ^ quadraticB3TailLine δ :=
        Real.rpow_le_rpow (by positivity) hratio hline
      _ = _ := (Real.rpow_mul hT0.le _ _).symm
  have hsmall : K ^ 2 * (P ^ 2 / (M * K)) ^ quadraticB3TailLine δ ≤ 1 := by
    calc
      _ ≤ (M * P) ^ 2 * (M * P) ^ (-δ * quadraticB3TailLine δ) :=
        mul_le_mul hKsq hpower (Real.rpow_nonneg (by positivity) _) (by positivity)
      _ = (M * P) ^ ((2 : ℝ) + -δ * quadraticB3TailLine δ) := by
        rw [← Real.rpow_two, ← Real.rpow_add hT0]
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hT (by nlinarith)
  calc
    _ = (M / P) * (K ^ 2 * (P ^ 2 / (M * K)) ^ quadraticB3TailLine δ) := by ring
    _ ≤ M / P := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hsmall (by positivity)

theorem quadraticB3_tail_monomial_eq {M P K : ℝ}
    (hM : 0 < M) (hP : 0 < P) (hK : 0 < K) (σ : ℝ) :
    M ^ (1 - σ) * P ^ (2 * σ - 1) * K ^ (2 - σ) =
      M / P * K ^ 2 * (P ^ 2 / (M * K)) ^ σ := by
  rw [Real.rpow_sub hM, Real.rpow_sub hP, Real.rpow_sub hK,
    Real.rpow_one, Real.rpow_one, Real.rpow_two,
    Real.div_rpow (sq_nonneg P) (mul_nonneg hM.le hK.le),
    Real.mul_rpow hM.le hK.le, ← Real.rpow_two P, ← Real.rpow_mul hP.le]
  ring

theorem quadraticB3_tail_monomial_bound {M P K δ : ℝ}
    (hM : 1 ≤ M) (hP : 1 ≤ P) (hδ : 0 < δ)
    (hlower : P ^ 2 / M * (M * P) ^ δ ≤ K)
    (hupper : K ≤ M * (M * P) ^ (-δ)) :
    M ^ (1 - quadraticB3TailLine δ) * P ^ (2 * quadraticB3TailLine δ - 1) *
        K ^ (2 - quadraticB3TailLine δ) ≤ M / P := by
  obtain ⟨hK0, _, _⟩ := quadraticB3_cutoff_range hM hP hδ hlower hupper
  rw [quadraticB3_tail_monomial_eq (zero_lt_one.trans_le hM) (zero_lt_one.trans_le hP) hK0]
  exact quadraticB3_tail_ratio_bound hM hP hδ hlower hupper

theorem quadraticB3_tail_pair_bound {M P K δ : ℝ}
    (hM : 1 ≤ M) (hP : 1 ≤ P) (hδ : 0 < δ)
    (hlower : P ^ 2 / M * (M * P) ^ δ ≤ K)
    (hupper : K ≤ M * (M * P) ^ (-δ)) :
    P * (M ^ (1 - quadraticB3TailLine δ) * P ^ (2 * quadraticB3TailLine δ - 1) *
        K ^ (2 - quadraticB3TailLine δ)) ≤ M := by
  have hP0 := zero_lt_one.trans_le hP
  calc
    _ ≤ P * (M / P) := mul_le_mul_of_nonneg_left
      (quadraticB3_tail_monomial_bound hM hP hδ hlower hupper) hP0.le
    _ = M := by field_simp

end
end ArtinMatthews.QuadraticScale
