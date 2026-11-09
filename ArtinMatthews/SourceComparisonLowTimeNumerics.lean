module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! The low-frequency rounding and squared truncation costs are absorbed
uniformly into the requested logarithmic saving. -/
namespace ArtinMatthews
open Filter
open scoped Topology

theorem sourceComparisonLowTime_truncation_absorb {L B E F A : ℝ}
    (hL : 1 ≤ L) (hB : 0 ≤ B) (hBL : 2 * B ≤ L)
    (hE : E ≤ L ^ (-(2 * (A + F + 1)))) :
    L ^ F * B * Real.sqrt E ≤ L ^ (-A) / 2 := by
  have hL₀ := zero_lt_one.trans_le hL
  have hS : Real.sqrt E ≤ L ^ (-(A + F + 1)) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨Real.rpow_nonneg hL₀.le _, ?_⟩
    rw [← Real.rpow_two, ← Real.rpow_mul hL₀.le]
    convert hE using 2; ring
  calc
    _ ≤ L ^ F * B * L ^ (-(A + F + 1)) :=
      mul_le_mul_of_nonneg_left hS (mul_nonneg (Real.rpow_nonneg hL₀.le _) hB)
    _ = B * (L ^ (-A) * L⁻¹) := by
      rw [mul_comm (L ^ F) B, mul_assoc, ← Real.rpow_add hL₀,
        show F + -(A + F + 1) = -A + (-1) by ring, Real.rpow_add hL₀, Real.rpow_neg_one]
    _ ≤ _ := by
      rw [mul_left_comm, ← div_eq_mul_inv, div_eq_mul_inv _ (2:ℝ)]
      exact mul_le_mul_of_nonneg_left ((div_le_iff₀ hL₀).mpr (by linarith))
        (Real.rpow_nonneg hL₀.le _)

theorem sourceComparisonLowTime_rounding_absorb_eventually {ε a B : ℝ}
    (hε : 0 < ε) (hεq : ε < 1/4) (ha : 0 < a) (hB : 0 < B) (C F S A : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ (Y N R k σ τ : ℝ),
      x ^ (1 - ε/4) ≤ Y → 0 ≤ N → N ≤ x ^ (1 - ε/2) + 1 →
      0 ≤ R → R ≤ x ^ (ε/8) →
      0 ≤ k → k ≤ (Real.log x) ^ C →
      |σ| ≤ (Real.log x) ^ S → |τ| ≤ (Real.log x) ^ S →
      let M := (Real.log x) ^ F
      (N / Y * (3 * k * (B * (M + M * |σ + τ| / a)))) * R ≤ (Real.log x) ^ (-A) / 2 := by
  let K := 12 * B * (1 + 2/a)
  let U := C + (F + max 0 S)
  have hK : 0 < K := by unfold K; positivity
  have hlim := (isLittleO_log_rpow_rpow_atTop (U + A) (by linarith : 0 < ε/8)).bound
    (inv_pos.mpr hK)
  filter_upwards [hlim, eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hxlim hx hL
  intro Y N R k σ τ hY hN₀ hN hR₀ hR hk₀ hk hσ hτ
  let L := Real.log x
  let M := L ^ F
  have hx₀ : 0 < x := zero_lt_one.trans hx
  have hL₀ : 0 < L := zero_lt_one.trans_le hL
  have hM : 0 ≤ M := Real.rpow_nonneg hL₀.le _
  have hxpow (d : ℝ) : 0 < x ^ d := Real.rpow_pos_of_pos hx₀ d
  have hY₀ : 0 < Y := (hxpow _).trans_le hY
  have hS : |σ + τ| ≤ 2 * L ^ max 0 S := by
    calc
      _ ≤ |σ| + |τ| := abs_add_le _ _
      _ ≤ L ^ S + L ^ S := add_le_add hσ hτ
      _ ≤ _ := by
        have h := Real.rpow_le_rpow_of_exponent_le hL (le_max_right 0 S)
        linarith only [h]
  have hM₀ : M ≤ L ^ (F + max 0 S) := by
    apply Real.rpow_le_rpow_of_exponent_le hL
    linarith only [le_max_left 0 S]
  have hM₁ : M * |σ + τ| / a ≤ (2/a) * L ^ (F + max 0 S) := by
    apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hS hM) ha.le).trans_eq
    unfold M
    rw [Real.rpow_add hL₀]
    ring
  have hCut : B * (M + M * |σ + τ| / a) ≤ B * (1 + 2/a) * L ^ (F + max 0 S) := by
    apply (mul_le_mul_of_nonneg_left (add_le_add hM₀ hM₁) hB.le).trans_eq
    ring
  have hN' : N ≤ 2 * x ^ (1 - ε/2) := by
    have h := Real.one_le_rpow hx.le (by linarith : 0 ≤ 1 - ε/2)
    linarith only [h, hN]
  have hRatio : N / Y ≤ 2 * x ^ (-(ε/4)) := by
    apply (div_le_div₀ (by positivity : 0 ≤ 2 * x ^ (1 - ε/2)) hN' (hxpow _) hY).trans_eq
    rw [mul_div_assoc, ← Real.rpow_sub hx₀]
    congr 2
    ring
  change ‖L ^ (U + A)‖ ≤ K⁻¹ * ‖x ^ (ε/8)‖ at hxlim
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hL₀.le _), Real.norm_of_nonneg (hxpow _).le] at hxlim
  have hLog : K * L ^ (U + A) ≤ x ^ (ε/8) := by
    apply (mul_le_mul_of_nonneg_left hxlim hK.le).trans_eq
    rw [← mul_assoc, mul_inv_cancel₀ hK.ne', one_mul]
  have hLast : K / 2 * L ^ U * x ^ (-(ε/8)) ≤ L ^ (-A) / 2 := by
    have hLpow : 0 < L ^ A := Real.rpow_pos_of_pos hL₀ A
    rw [Real.rpow_neg hL₀.le, Real.rpow_neg hx₀.le]
    calc
      _ = (K * L ^ (U + A) / x ^ (ε/8)) * ((L ^ A)⁻¹ / 2) := by
        rw [Real.rpow_add hL₀ U A]
        field_simp [hLpow.ne', (hxpow (ε/8)).ne']
      _ ≤ 1 * ((L ^ A)⁻¹ / 2) :=
        mul_le_mul_of_nonneg_right ((div_le_one (hxpow _)).mpr hLog) (by positivity)
      _ = _ := one_mul _
  change (N / Y * (3 * k * (B * (M + M * |σ + τ| / a)))) * R ≤ L ^ (-A) / 2
  calc
    _ ≤ (2 * x ^ (-(ε/4)) * (3 * L ^ C * (B * (1 + 2/a) * L ^ (F + max 0 S)))) *
          x ^ (ε/8) := by
      gcongr
    _ = K / 2 * L ^ U * x ^ (-(ε/8)) := by
      unfold K U
      rw [Real.rpow_add hL₀ C (F + max 0 S)]
      have hp : x ^ (-(ε/4)) * x ^ (ε/8) = x ^ (-(ε/8)) := by
        rw [← Real.rpow_add hx₀]
        congr 1
        ring
      rw [← hp]
      ring
    _ ≤ _ := hLast

end ArtinMatthews
