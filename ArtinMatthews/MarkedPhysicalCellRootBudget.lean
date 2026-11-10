module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset


set_option backward.privateInPublic true
@[expose] public section

/-! The actual stronger L^.21 versus L^.5 hierarchy controls the cell
factor after the 2R-th root. We retain this hierarchy explicitly. -/
namespace ArtinMatthews
noncomputable section

def markedPhysicalMomentOrder (L : ℝ) : ℕ := 2*⌈L^(1/2:ℝ)/2⌉₊

theorem markedPhysicalMomentOrder_lower (L : ℝ) :
    L^(1/2:ℝ)≤(markedPhysicalMomentOrder L:ℝ) := by
  have h := Nat.le_ceil (L^(1/2:ℝ)/2)
  simp only [markedPhysicalMomentOrder,Nat.cast_mul,Nat.cast_ofNat]
  linarith

theorem markedPhysicalCell_root_budget (H C L : ℝ) (hH : 1≤H) (hC : 0≤C) (hL : 1≤L)
    (hlog : Real.log H≤C*L^(21/100:ℝ)) (n : ℕ) (hn : L^(1/2:ℝ)≤(n:ℝ)) :
    (256*H+1)^((n:ℝ)⁻¹)≤257*Real.exp C := by
  have hn1 : 1≤(n:ℝ) :=
    (Real.one_le_rpow hL (by norm_num : (0:ℝ)≤1/2)).trans hn
  have hnp : 0<(n:ℝ) := by linarith
  have hHp : 0<H := by linarith
  have hf : 0<256*H+1 := by positivity
  have hmono : L^(21/100:ℝ)≤(n:ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (21/100:ℝ)≤1/2)).trans hn
  have hsmall : Real.log (256*H+1)≤Real.log 257+C*(n:ℝ) := by
    calc
      _ ≤ Real.log (257*H) := Real.log_le_log hf (by linarith)
      _ = Real.log 257+Real.log H := Real.log_mul (by norm_num) hHp.ne'
      _ ≤ Real.log 257+C*(n:ℝ) := add_le_add_right (hlog.trans (mul_le_mul_of_nonneg_left hmono hC)) _
  have hbudget : Real.log (256*H+1)≤(Real.log 257+C)*(n:ℝ) := by
    have hl : 0≤Real.log 257 := Real.log_nonneg (by norm_num)
    have hh := mul_le_mul_of_nonneg_left hn1 hl
    nlinarith
  rw [Real.rpow_def_of_pos hf]
  calc
    _ ≤ Real.exp (Real.log 257+C) := Real.exp_le_exp.mpr (by
      have hh := mul_le_mul_of_nonneg_right hbudget (inv_nonneg.mpr hnp.le)
      simpa only [mul_assoc,mul_inv_cancel₀ hnp.ne',mul_one] using hh)
    _ = 257*Real.exp C := by rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<257)]

theorem markedPhysicalCell_root_budget_source_order
    (H C L : ℝ) (hH : 1≤H) (hC : 0≤C) (hL : 1≤L)
    (hlog : Real.log H≤C*L^(21/100:ℝ)) :
    (256*H+1)^((markedPhysicalMomentOrder L:ℝ)⁻¹)≤257*Real.exp C :=
  markedPhysicalCell_root_budget H C L hH hC hL hlog _ (markedPhysicalMomentOrder_lower L)

end
end ArtinMatthews
