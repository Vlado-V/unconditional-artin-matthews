module

public import ArtinMatthews.ShiftedReciprocalSquare
public import Mathlib.Analysis.SpecialFunctions.Pow.Real


set_option backward.privateInPublic true
@[expose] public section

/-! A uniform square-sum bound for subpower coefficients against a genuinely
decaying weight. The scale dependence follows from an exact telescoping sum. -/

noncomputable section
namespace ArtinMatthews

theorem shifted_weighted_square_point (ε S Ca Cb x : ℝ)
    (hε : 0 < ε) (hεtwo : ε ≤ 2) (hS : 0 < S) (hCa : 0 ≤ Ca) (_hCb : 0 ≤ Cb)
    (hx : 0 < x) (a b : ℂ) (ha : ‖a‖^2 ≤ Ca * x^ε)
    (hb : (1 + x / S)^2 * ‖b‖ ≤ Cb) :
    ‖a * b‖^2 ≤ (Ca * Cb^2 * S^ε) * (1 / (1 + x / S)^2) := by
  let t := 1 + x / S
  have ht : 1 ≤ t := by
    dsimp [t]
    linarith [div_pos hx hS]
  have htp : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hxp : x ≤ S * t := by dsimp [t]; field_simp; nlinarith
  have hxpow : x^ε ≤ S^ε * t^2 := by
    calc
      _ ≤ (S * t)^ε := Real.rpow_le_rpow hx.le hxp hε.le
      _ = S^ε * t^ε := Real.mul_rpow hS.le htp.le
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (by simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le ht hεtwo)
        (Real.rpow_nonneg hS.le ε)
  have ha' : ‖a‖^2 ≤ Ca * S^ε * t^2 := by
    calc
      _ ≤ Ca * x^ε := ha
      _ ≤ Ca * (S^ε * t^2) := mul_le_mul_of_nonneg_left hxpow hCa
      _ = _ := by ring
  have hb' : t^4 * ‖b‖^2 ≤ Cb^2 := by
    have hs := pow_le_pow_left₀ (by positivity : 0 ≤ t^2 * ‖b‖) hb 2
    nlinarith only [hs]
  rw [norm_mul, mul_pow]
  change ‖a‖^2 * ‖b‖^2 ≤ (Ca * Cb^2 * S^ε) * (1 / t^2)
  rw [mul_one_div]
  apply (le_div_iff₀ (sq_pos_of_pos htp)).mpr
  calc
    _ ≤ (Ca * S^ε * t^2) * ‖b‖^2 * t^2 := by gcongr
    _ = Ca * S^ε * (t^4 * ‖b‖^2) := by ring
    _ ≤ Ca * S^ε * Cb^2 := mul_le_mul_of_nonneg_left hb' (by positivity)
    _ = _ := by ring

theorem shifted_weighted_square_sum (ε S Ca Cb : ℝ)
    (hε : 0 < ε) (hεtwo : ε ≤ 2) (hS : 0 < S) (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb)
    (a b : ℕ → ℂ)
    (ha : ∀ n : ℕ, ‖a (n + 1)‖^2 ≤ Ca * ((n + 1 : ℕ) : ℝ)^ε)
    (hb : ∀ n : ℕ, (1 + ((n + 1 : ℕ) : ℝ) / S)^2 * ‖b (n + 1)‖ ≤ Cb) :
    Summable (fun n : ℕ => ‖a (n + 1) * b (n + 1)‖^2) ∧
      (∑' n : ℕ, ‖a (n + 1) * b (n + 1)‖^2) ≤ Ca * Cb^2 * S^(1 + ε) := by
  obtain ⟨hs, hsum⟩ := shifted_reciprocal_square_sum S hS
  have hp (n : ℕ) := shifted_weighted_square_point ε S Ca Cb ((n + 1 : ℕ) : ℝ)
    hε hεtwo hS hCa hCb (by positivity) (a (n + 1)) (b (n + 1)) (ha n) (hb n)
  have hmajor := hs.mul_left (Ca * Cb^2 * S^ε)
  have hsmall : Summable (fun n : ℕ => ‖a (n + 1) * b (n + 1)‖^2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hp hmajor
  refine ⟨hsmall, ?_⟩
  calc
    _ ≤ ∑' n : ℕ, (Ca * Cb^2 * S^ε) * (1 / (1 + ((n + 1 : ℕ) : ℝ) / S)^2) :=
      hsmall.tsum_le_tsum hp hmajor
    _ = (Ca * Cb^2 * S^ε) * ∑' n : ℕ, 1 / (1 + ((n + 1 : ℕ) : ℝ) / S)^2 := tsum_mul_left
    _ ≤ (Ca * Cb^2 * S^ε) * S := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = Ca * Cb^2 * S^(1 + ε) := by rw [Real.rpow_add hS, Real.rpow_one]; ring

end ArtinMatthews
