module

public import ArtinMatthews.GiantSamplingDyads
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics


set_option backward.privateInPublic true
@[expose] public section

/-! The original squarepart cutoff and modulus range save a fixed power
on every supported cofactor dyad. -/

noncomputable section
namespace ArtinMatthews

open Filter
open scoped BigOperators Topology

theorem giantSampling_square_cutoff_sq {x ε : ℝ} (hx : 0 ≤ x) :
    (x ^ (ε / 32)) ^ 2 = x ^ (ε / 16) := by
  rw [← Real.rpow_mul_natCast hx]
  congr 1
  push_cast
  ring

theorem giantSampling_source_cutoffs_eventually {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ x ∧ 4 ≤ x ^ (ε / 32) ∧
      (x ^ (ε / 32)) ^ 2 ≤ x ^ (ε / 2) / 2 := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop (show 0 < ε / 32 by positivity)).eventually (eventually_ge_atTop 4),
    (tendsto_rpow_atTop (show 0 < 7 * ε / 16 by positivity)).eventually (eventually_ge_atTop 2)] with
    x hx hD hpow
  have hx₀ := zero_lt_one.trans_le hx
  refine ⟨hx, hD, ?_⟩
  rw [giantSampling_square_cutoff_sq hx₀.le]
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  calc
    _ ≤ x ^ (ε / 16) * x ^ (7 * ε / 16) :=
      mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hx₀.le _)
    _ = _ := by rw [← Real.rpow_add hx₀]; congr 1; ring

theorem giantSampling_source_smallBudget_le {x ε T : ℝ}
    (hx : 1 ≤ x) (hε : 0 < ε) (hεq : ε < 1 / 4)
    (hTlo : x ^ (ε / 2) / 2 ≤ T) (hThi : T ≤ 2 * x ^ ε) :
    let R := ⌊x ^ (ε / 64)⌋₊
    let D := x ^ (ε / 32)
    let ν := ε / 1024
    (R : ℝ) ^ 2 * x ^ ν * (x * T ^ (-(1 / 2) : ℝ) * D ^ 2 +
      x ^ (7 / 8 : ℝ) * (2 * T) ^ (3 / 8 : ℝ) * (4 * D ^ (1 / 4 : ℝ))) ≤
      ((2 : ℝ) ^ (1 / 2 : ℝ) + 4 * (4 : ℝ) ^ (3 / 8 : ℝ)) * x ^ (1 - ε / 64) := by
  let R := ⌊x ^ (ε / 64)⌋₊
  let D := x ^ (ε / 32)
  let ν := ε / 1024
  let a := (2 : ℝ) ^ (1 / 2 : ℝ)
  let b := 4 * (4 : ℝ) ^ (3 / 8 : ℝ)
  have hx₀ := zero_lt_one.trans_le hx
  have hTmin : 0 < x ^ (ε / 2) / 2 := by positivity
  have hT := hTmin.trans_le hTlo
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := by positivity
  have hR : (R : ℝ) ^ 2 ≤ x ^ (ε / 32) := by
    calc
      _ ≤ (x ^ (ε / 64)) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le (Real.rpow_nonneg hx₀.le _)) 2
      _ = _ := by rw [← Real.rpow_mul_natCast hx₀.le]; congr 1; push_cast; ring
  have hD : D ^ (1 / 4 : ℝ) = x ^ (ε / 128) := by
    dsimp only [D]
    rw [← Real.rpow_mul hx₀.le]
    congr 1
    ring
  have hlow : T ^ (-(1 / 2) : ℝ) ≤ a * x ^ (-ε / 4) := by
    calc
      _ ≤ (x ^ (ε / 2) / 2) ^ (-(1 / 2) : ℝ) := by
        rw [Real.rpow_neg hT.le, Real.rpow_neg hTmin.le]
        exact (inv_le_inv₀ (Real.rpow_pos_of_pos hT _) (Real.rpow_pos_of_pos hTmin _)).mpr
          (Real.rpow_le_rpow hTmin.le hTlo (by norm_num))
      _ = _ := by
        rw [Real.div_rpow (Real.rpow_nonneg hx₀.le _) (by norm_num) _,
          ← Real.rpow_mul hx₀.le, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
          div_inv_eq_mul, show ε / 2 * (-(1 / 2) : ℝ) = -ε / 4 by ring]
        exact mul_comm _ _
  have hhigh : (2 * T) ^ (3 / 8 : ℝ) ≤ (4 : ℝ) ^ (3 / 8 : ℝ) * x ^ (ε * (3 / 8)) := by
    calc
      _ ≤ (4 * x ^ ε) ^ (3 / 8 : ℝ) :=
        Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
      _ = _ := by
        rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hx₀.le _), ← Real.rpow_mul hx₀.le]
  have h₁ : x * T ^ (-(1 / 2) : ℝ) * D ^ 2 ≤ a * x ^ (1 + -ε / 4 + ε / 16) := by
    calc
      _ ≤ x * (a * x ^ (-ε / 4)) * D ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlow hx₀.le) (sq_nonneg _)
      _ = _ := by
        rw [show D ^ 2 = x ^ (ε / 16) from giantSampling_square_cutoff_sq hx₀.le]
        simp only [Real.rpow_add hx₀, Real.rpow_one]
        ring
  have h₂ : x ^ (7 / 8 : ℝ) * (2 * T) ^ (3 / 8 : ℝ) * (4 * D ^ (1 / 4 : ℝ)) ≤
      b * x ^ (7 / 8 + ε * (3 / 8) + ε / 128) := by
    rw [hD]
    calc
      _ ≤ x ^ (7 / 8 : ℝ) * ((4 : ℝ) ^ (3 / 8 : ℝ) * x ^ (ε * (3 / 8))) *
          (4 * x ^ (ε / 128)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhigh (by positivity)) (by positivity)
      _ = _ := by simp only [Real.rpow_add hx₀, b]; ring
  change (R : ℝ) ^ 2 * x ^ ν * _ ≤ (a + b) * _
  calc
    _ ≤ (x ^ (ε / 32) * x ^ ν) *
        (a * x ^ (1 + -ε / 4 + ε / 16) + b * x ^ (7 / 8 + ε * (3 / 8) + ε / 128)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hR (Real.rpow_nonneg hx₀.le _))
        (add_le_add h₁ h₂) (by positivity) (by positivity)
    _ = a * x ^ (ε / 32 + ν + (1 + -ε / 4 + ε / 16)) +
        b * x ^ (ε / 32 + ν + (7 / 8 + ε * (3 / 8) + ε / 128)) := by
      simp only [Real.rpow_add hx₀, Real.rpow_one]
      ring
    _ ≤ a * x ^ (1 - ε / 64) + b * x ^ (1 - ε / 64) :=
      add_le_add
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx (by dsimp [ν]; linarith)) ha)
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx (by dsimp [ν]; linarith)) hb)
    _ = _ := by ring

theorem giantSampling_source_largeBudget_le {x ε : ℝ} (hx : 1 ≤ x) (hε : 0 < ε) :
    x ^ (1 + 2 * (ε / 1024)) / x ^ (ε / 32) ≤ x ^ (1 - ε / 64) := by
  rw [← Real.rpow_sub (zero_lt_one.trans_le hx)]
  exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)

theorem giantSampling_active_dyad_card_subpower {x ε : ℝ} (hx : 1 ≤ x) (hε : 0 < ε) :
    ((giantSamplingDyadIndices (giantSamplingActiveCofactors x ε)).card : ℝ) ≤
      (2 + 128 / Real.log 2) * x ^ (ε / 128) := by
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := Real.log_le_rpow_div (zero_le_one.trans hx) (show 0 < ε / 128 by positivity)
  calc
    _ ≤ 2 + (ε / Real.log 2) * Real.log x := giantSampling_active_dyad_card_le hx hε.le
    _ ≤ 2 * x ^ (ε / 128) + (ε / Real.log 2) * (x ^ (ε / 128) / (ε / 128)) := by
      apply add_le_add
      · simpa only [mul_one] using
          mul_le_mul_of_nonneg_left (Real.one_le_rpow hx (show 0 ≤ ε / 128 by positivity))
            (by norm_num : (0 : ℝ) ≤ 2)
      · exact mul_le_mul_of_nonneg_left h (div_nonneg hε.le hlog₂.le)
    _ = _ := by field_simp [hε.ne', hlog₂.ne']

end ArtinMatthews
