module

public import ArtinMatthews.MarkedMinorArcDirtyScalar
public import ArtinMatthews.MarkedBonferroniTail
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
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
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! Actual B=ceil(log²), logarithmic arc cutoff and exponential band/box
scale give every logarithmic saving for the major comparison row. -/
noncomputable section
namespace ArtinMatthews

open Filter
open scoped Topology

def markedDirtyMajorEnvelope (C : ℝ) (groups : ℕ) (A₀ x : ℝ) : ℝ :=
  C*(markedDirtyMemoryCutoff x+1:ℝ)^groups*((Real.log x)^A₀)^3*
    Real.exp (-(1/10:ℝ)*(Real.log x)^(1/10:ℝ))

theorem markedDirtyMajor_tail_le {L Y : ℝ} (hL : 0 ≤ L) (hY : Real.exp (L^(1/10:ℝ)) ≤ Y) :
    Real.exp (-(L^(1/10:ℝ)))+Y^(-1/10:ℝ) ≤ 2*Real.exp (-(1/10:ℝ)*L^(1/10:ℝ)) := by
  have he : Real.exp (-(L^(1/10:ℝ))) ≤ Real.exp (-(1/10:ℝ)*L^(1/10:ℝ)) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.rpow_nonneg hL (1/10:ℝ)])
  have hp : Y^(-1/10:ℝ) ≤ Real.exp (-(1/10:ℝ)*L^(1/10:ℝ)) := by
    apply (Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) hY (by norm_num : (-1/10:ℝ)≤0)).trans_eq
    rw [← Real.exp_mul]
    congr 1
    ring
  linarith

theorem markedDirtyMemoryCutoff_succ_pow_le (groups : ℕ) {x : ℝ} (hx : 1 ≤ Real.log x) :
    (markedDirtyMemoryCutoff x+1:ℝ)^groups ≤ (3:ℝ)^groups*(Real.log x)^(2*(groups:ℝ)) := by
  have hb := markedDirtyMemoryCutoff_le hx
  have hL : 0 < Real.log x := by linarith
  have hb1 : (markedDirtyMemoryCutoff x+1:ℝ) ≤ 3*(Real.log x)^(2:ℝ) := by
    rw [Real.rpow_two] at hb ⊢
    have hsq := one_le_pow₀ hx (n := 2)
    nlinarith
  calc
    _ ≤ (3*(Real.log x)^(2:ℝ))^groups := pow_le_pow_left₀ (by positivity) hb1 _
    _ = _ := by rw [mul_pow,← Real.rpow_mul_natCast hL.le]

theorem markedDirtyMajorEnvelope_log_tendsto {C : ℝ} (hC : 0 ≤ C) (groups : ℕ) (A₀ A : ℝ) :
    Tendsto (fun x : ℝ => (Real.log x)^A*markedDirtyMajorEnvelope C groups A₀ x) atTop (nhds 0) := by
  have ht := ((rpow_mul_exp_neg_rpow_tendsto (A+2*(groups:ℝ)+3*A₀)
    (by norm_num : (0:ℝ)<1/10) (by norm_num : (0:ℝ)<1/10)).comp Real.tendsto_log_atTop).const_mul
      (C*(3:ℝ)^groups)
  simp only [mul_zero,Function.comp_def] at ht
  apply squeeze_zero' ?_ ?_ ht
  · filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hx
    unfold markedDirtyMajorEnvelope
    positivity
  · filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hx
    have hL : 0 < Real.log x := by linarith
    have hb := markedDirtyMemoryCutoff_succ_pow_le groups hx
    calc
      _ ≤ (Real.log x)^A*(C*((3:ℝ)^groups*(Real.log x)^(2*(groups:ℝ)))*((Real.log x)^A₀)^3*
          Real.exp (-(1/10:ℝ)*(Real.log x)^(1/10:ℝ))) := by
        unfold markedDirtyMajorEnvelope
        gcongr
      _ = _ := by
        rw [← Real.rpow_mul_natCast hL.le]
        norm_num only [Nat.cast_ofNat]
        rw [show A₀*(3:ℝ)=3*A₀ by ring,Real.rpow_add hL,Real.rpow_add hL]
        ring

end ArtinMatthews
