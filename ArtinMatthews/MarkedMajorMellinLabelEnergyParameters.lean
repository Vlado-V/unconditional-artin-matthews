module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
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

/-! Exact scale ranges for the actual central radius 2*X*L^B. -/
namespace ArtinMatthews
open Filter

theorem markedMajorLabelEnergy_height_parameters (B σ Kx : ℝ) (hB : 0 ≤ B) :
    ∀ᶠ L : ℝ in atTop, ∀ X : ℝ, 1 ≤ X → X ≤ Real.exp (σ*L) → X ≤ Kx*Real.exp L →
      1 < 2*X*L^B ∧ Real.log (2*X*L^B) ≤ (σ+1)*L ∧
        2*X*L^B ≤ (2*Kx)*Real.exp L*L^B ∧ (2*X*L^B)/X ≤ L^(B+1) := by
  have hp := (isLittleO_rpow_exp_atTop B).bound (by norm_num : (0:ℝ)<1/2)
  filter_upwards [hp,eventually_ge_atTop (2:ℝ)] with L hp hL
  have hLp : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hpow : 1 ≤ L^B := Real.one_le_rpow hL1 hB
  have hpoly : 2*L^B ≤ Real.exp L := by
    simp only [Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hLp _),
      abs_of_pos (Real.exp_pos _)] at hp
    linarith
  intro X hX hupper hcomp
  have hXp : 0 < X := by linarith
  have hTp : 0 < 2*X*L^B := by positivity
  refine ⟨by nlinarith,?_,?_,?_⟩
  · apply (Real.log_le_iff_le_exp hTp).mpr
    calc
      2*X*L^B = X*(2*L^B) := by ring
      _ ≤ Real.exp (σ*L)*Real.exp L :=
        mul_le_mul hupper hpoly (by positivity) (Real.exp_pos _).le
      _ = Real.exp ((σ+1)*L) := by rw [← Real.exp_add]; congr 1; ring
  · have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcomp (by norm_num : (0:ℝ)≤2))
      (Real.rpow_nonneg hLp.le B)
    simpa only [mul_assoc] using h
  · calc
      (2*X*L^B)/X = 2*L^B := by field_simp
      _ ≤ L*L^B := mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg hLp.le B)
      _ = L^(B+1) := by rw [Real.rpow_add hLp,Real.rpow_one]; ring

theorem markedMajorLabelEnergy_theta_scale {L A Kθ θ : ℝ}
    (hL : 1 ≤ L) (hA : 0 ≤ A) (hθ : |θ| ≤ Kθ*L^A) :
    1+|θ| ≤ (1+Kθ)*L^A := by
  have hp := Real.one_le_rpow hL hA
  nlinarith

end ArtinMatthews
