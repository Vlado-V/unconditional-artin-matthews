module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt


set_option backward.privateInPublic true
@[expose] public section

/-! The complete numerical core/tail budget. The decay order is fixed
before L tends to infinity and every frequency scale remains explicit. -/
namespace ArtinMatthews
open Filter

theorem markedMajorLabelEnergy_tail_factor {L A W : ℝ} (hL : 1 ≤ L) (hW : 0 < W)
    (hWL : W ≤ L^(A+1)) (n : ℕ) :
    ((1+L^(A+2)/W)^n)⁻¹ ≤ L^(-(n : ℝ)) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hratio : L ≤ L^(A+2)/W := by
    apply (le_div_iff₀ hW).mpr
    calc
      L*W ≤ L*L^(A+1) := mul_le_mul_of_nonneg_left hWL hLp.le
      _ = L^(A+2) := by
        conv_lhs => lhs; rw [← Real.rpow_one L]
        rw [← Real.rpow_add hLp]
        congr 1
        ring
  rw [Real.rpow_neg hLp.le,Real.rpow_natCast]
  exact inv_anti₀ (pow_pos hLp _) (pow_le_pow_left₀ hLp.le (by linarith) _)

theorem markedMajorLabelEnergy_log_budget (A D P Kθ CF CM mass : ℝ)
    (hCF : 0 ≤ CF) (hCM : 0 ≤ CM) (hmass : 0 ≤ mass)
    (n : ℕ) (hn : P+2*A+2*D+9 ≤ (n : ℝ)) :
    ∀ᶠ L : ℝ in atTop, ∀ W : ℝ, 1 ≤ W → W ≤ (1+Kθ)*L^A →
      CF*(2*L^(A+2))*L^(-(A+2+P+2)) +
        CF*((1+L^(A+2)/W)^n)⁻¹*(CM*W*L^(2*D+5))*(W*mass) ≤ L^(-P) := by
  let Z := 2*CF+CF*CM*mass
  filter_upwards [eventually_ge_atTop (max 1 (max (1+Kθ) Z))] with L hL
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hKL : 1+Kθ ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hZL : Z ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  intro W hW hWK
  have hWp : 0 < W := zero_lt_one.trans_le hW
  have hWL : W ≤ L^(A+1) := by
    calc
      _ ≤ (1+Kθ)*L^A := hWK
      _ ≤ L*L^A := mul_le_mul_of_nonneg_right hKL (Real.rpow_nonneg hLp.le _)
      _ = _ := by rw [Real.rpow_add hLp,Real.rpow_one]; ring
  have htail := markedMajorLabelEnergy_tail_factor hL1 hWp hWL n
  have hWsquare : W^2 ≤ L^(2*(A+1)) := by
    calc
      _ ≤ (L^(A+1))^2 := pow_le_pow_left₀ hWp.le hWL 2
      _ = _ := by rw [mul_comm (2:ℝ),Real.rpow_mul hLp.le,Real.rpow_two]
  have hcore : CF*(2*L^(A+2))*L^(-(A+2+P+2)) = 2*CF*L^(-P-2) := by
    have hp : L^(A+2)*L^(-(A+2+P+2)) = L^(-P-2) := by
      rw [← Real.rpow_add hLp]
      congr 1
      ring
    calc
      _ = (2*CF)*(L^(A+2)*L^(-(A+2+P+2))) := by ring
      _ = _ := by rw [hp]
  have htailbound : CF*((1+L^(A+2)/W)^n)⁻¹*(CM*W*L^(2*D+5))*(W*mass) ≤
      (CF*CM*mass)*L^(-P-2) := by
    have hfac : 0 ≤ CF*CM*mass := mul_nonneg (mul_nonneg hCF hCM) hmass
    calc
      _ = (CF*CM*mass)*(((1+L^(A+2)/W)^n)⁻¹*W^2*L^(2*D+5)) := by ring
      _ ≤ (CF*CM*mass)*(L^(-(n:ℝ))*L^(2*(A+1))*L^(2*D+5)) := by
        apply mul_le_mul_of_nonneg_left _ hfac
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul htail hWsquare (sq_nonneg _) (Real.rpow_nonneg hLp.le _))
          (Real.rpow_nonneg hLp.le _)
      _ = (CF*CM*mass)*L^(-(n:ℝ)+2*(A+1)+(2*D+5)) := by
        rw [← Real.rpow_add hLp,← Real.rpow_add hLp]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)) hfac
  calc
    _ ≤ 2*CF*L^(-P-2)+(CF*CM*mass)*L^(-P-2) := add_le_add hcore.le htailbound
    _ = Z*L^(-P-2) := by dsimp [Z]; ring
    _ ≤ L*L^(-P-2) := mul_le_mul_of_nonneg_right hZL (Real.rpow_nonneg hLp.le _)
    _ = L^(-P-1) := by
      conv_lhs => lhs; rw [← Real.rpow_one L]
      rw [← Real.rpow_add hLp]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)

end ArtinMatthews
