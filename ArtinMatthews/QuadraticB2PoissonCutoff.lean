module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real


set_option backward.privateInPublic true
@[expose] public section

/-! The same cutoff is admissible at every shorter column length.
Keeping its initial scale in the Poisson term avoids changing a row
cutoff during the descent. -/
namespace ArtinMatthews.QuadraticScale

noncomputable section

def poissonCutoff (M N δ : ℝ) : ℝ := max 1 (N ^ 2 / M * (M * N) ^ δ)

def poissonMainScale (M N a : ℝ) : ℝ := M + N + N ^ (2 * a - 1) * M ^ (1 - a)

theorem poissonMainScale_nonneg {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N) (a : ℝ) :
    0 ≤ poissonMainScale M N a := by
  unfold poissonMainScale
  positivity

theorem poissonCutoff_range {M N L δ : ℝ} (hM : 1 ≤ M) (hN : 1 ≤ N) (hδ : 0 ≤ δ)
    (hsep : 2 * N * (M * N) ^ δ ≤ M) (hL : 1 ≤ L) (hLN : L ≤ N) :
    1 ≤ poissonCutoff M N δ ∧ poissonCutoff M N δ ≤ M / 2 ∧
      L ^ 2 / M * (M * L) ^ δ ≤ poissonCutoff M N δ ∧
      poissonCutoff M N δ ≤ M * (M * L) ^ (-δ) := by
  let U := (M * N) ^ δ
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hU : 1 ≤ U := Real.one_le_rpow (one_le_mul_of_one_le_of_one_le hM hN) hδ
  have hU0 : 0 < U := zero_lt_one.trans_le hU
  have hNU : N ≤ N * U := le_mul_of_one_le_right hN0.le hU
  have hsep' : 2 * (N * U) ≤ M := by simpa only [mul_assoc] using hsep
  have hN2 : 2 * N ≤ M :=
    (mul_le_mul_of_nonneg_left hNU (by norm_num : 0 ≤ (2 : ℝ))).trans hsep'
  have hb : N ^ 2 / M * U ≤ N / 2 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hM0).mpr
    have hh := mul_le_mul_of_nonneg_left hsep (show 0 ≤ N / 2 by positivity)
    nlinarith
  have hdiv : 2 * N ≤ M / U := (le_div_iff₀ hU0).mpr hsep
  refine ⟨le_max_left _ _, max_le (by linarith) (hb.trans (by linarith)), ?_, ?_⟩
  · apply le_trans _ (le_max_right 1 _)
    refine mul_le_mul (div_le_div_of_nonneg_right
      (pow_le_pow_left₀ hL0.le hLN 2) hM0.le) ?_ (by positivity) (by positivity)
    exact Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left hLN hM0.le) hδ
  · have hK : poissonCutoff M N δ ≤ M / U :=
      max_le (by linarith) (hb.trans (by linarith))
    calc
      _ ≤ M / U := hK
      _ = M * (M * N) ^ (-δ) := by
        rw [Real.rpow_neg (by positivity : 0 ≤ M * N)]
        rfl
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (by positivity)
          (mul_le_mul_of_nonneg_left hLN hM0.le) (neg_nonpos.mpr hδ)) hM0.le

private theorem poissonCutoff_raw_power {M N δ a : ℝ} (hM : 0 < M) (hN : 0 < N) :
    Real.sqrt M * (N ^ 2 / M * (M * N) ^ δ) ^ (a - 1 / 2) =
      (N ^ (2 * a - 1) * M ^ (1 - a)) * (M * N) ^ (δ * (a - 1 / 2)) := by
  have hT : 0 < M * N := mul_pos hM hN
  have hNexp : (2 : ℝ) * (a - 1 / 2) = 2 * a - 1 := by ring
  have hMexp : (1 / 2 : ℝ) + -(a - 1 / 2) = 1 - a := by ring
  rw [Real.sqrt_eq_rpow, Real.mul_rpow (by positivity) (Real.rpow_nonneg hT.le _),
    Real.div_rpow (sq_nonneg N) hM.le, ← Real.rpow_two N, ← Real.rpow_mul hN.le,
    ← Real.rpow_mul hT.le, hNexp,
    div_eq_mul_inv (N ^ (2 * a - 1)) (M ^ (a - 1 / 2)), ← Real.rpow_neg hM.le]
  calc
    _ = (N ^ (2 * a - 1) * (M ^ (1 / 2 : ℝ) * M ^ (-(a - 1 / 2)))) *
        (M * N) ^ (δ * (a - 1 / 2)) := by ac_rfl
    _ = _ := by rw [← Real.rpow_add hM, hMexp]

theorem poissonCutoff_block_le {M N L δ a : ℝ} (hM : 1 ≤ M) (hN : 1 ≤ N)
    (hL : 1 ≤ L) (hLN : L ≤ N) (hδ : 0 ≤ δ) (ha : 1 ≤ a) :
    M + L + Real.sqrt M * poissonCutoff M N δ ^ (a - 1 / 2) +
        Real.sqrt (M / poissonCutoff M N δ) * L ≤
      3 * poissonMainScale M N a * (M * N) ^ (δ * (a - 1 / 2)) := by
  let K := poissonCutoff M N δ
  let U := (M * N) ^ (δ * (a - 1 / 2))
  let V := N ^ (2 * a - 1) * M ^ (1 - a)
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hT : 1 ≤ M * N := one_le_mul_of_one_le_of_one_le hM hN
  have hU : 1 ≤ U := Real.one_le_rpow hT (mul_nonneg hδ (by linarith))
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hK : N ^ 2 / M ≤ K :=
    (le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hT hδ)).trans (le_max_right _ _)
  have hK0 : 0 < K := (show 0 < N ^ 2 / M by positivity).trans_le hK
  have hT₁ : Real.sqrt (M / K) * L ≤ M := by
    have hdiv : M / K ≤ (M / N) ^ 2 := by
      calc
        _ ≤ M / (N ^ 2 / M) := div_le_div_of_nonneg_left hM0.le (by positivity) hK
        _ = _ := by field_simp
    have hs := Real.sqrt_le_sqrt hdiv
    rw [Real.sqrt_sq (div_nonneg hM0.le hN0.le)] at hs
    calc
      _ ≤ (M / N) * N := mul_le_mul hs hLN (zero_le_one.trans hL) (by positivity)
      _ = _ := div_mul_cancel₀ M hN0.ne'
  have hT₂ : Real.sqrt M * K ^ (a - 1 / 2) ≤ (M + V) * U := by
    rcases le_total (N ^ 2 / M * (M * N) ^ δ) 1 with h | h
    · have hK1 : K = 1 := max_eq_left h
      rw [hK1, Real.one_rpow, mul_one]
      calc
        _ ≤ M := Real.sqrt_le_self_iff.mpr (Or.inr hM)
        _ ≤ M + V := le_add_of_nonneg_right hV
        _ ≤ _ := le_mul_of_one_le_right (by positivity) hU
    · have hK1 : K = N ^ 2 / M * (M * N) ^ δ := max_eq_right h
      rw [hK1, poissonCutoff_raw_power hM0 hN0]
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hM0.le) (zero_le_one.trans hU)
  have hMU : M ≤ M * U := le_mul_of_one_le_right hM0.le hU
  have hNU : N ≤ N * U := le_mul_of_one_le_right hN0.le hU
  have hVU : 0 ≤ V * U := mul_nonneg hV (zero_le_one.trans hU)
  change M + L + Real.sqrt M * K ^ (a - 1 / 2) + Real.sqrt (M / K) * L ≤ 3 * (M + N + V) * U
  nlinarith

end
end ArtinMatthews.QuadraticScale
