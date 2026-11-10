module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! A concrete smooth test supported away from zero at a complex place.
The exponent -1/3 is the additive-density form of
|z|_v^(5/6) d^×z with |z|_v = ‖z‖². -/

namespace ArtinMatthews.VaryingKummerAnalytic
open MeasureTheory
open scoped ContDiff Topology
noncomputable section

def sourceAnnularBump : ContDiffBump (1 : ℂ) where
  rIn := 1 / 8
  rOut := 1 / 4
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

theorem sourceAnnularBump_smooth : ContDiff ℝ ∞ sourceAnnularBump :=
  sourceAnnularBump.contDiff

theorem sourceAnnularBump_compact : HasCompactSupport sourceAnnularBump :=
  sourceAnnularBump.hasCompactSupport

theorem sourceAnnularBump_nonneg (z : ℂ) : 0 ≤ sourceAnnularBump z :=
  sourceAnnularBump.nonneg

theorem sourceAnnularBump_one : sourceAnnularBump (1 : ℂ) = 1 :=
  sourceAnnularBump.one_of_mem_closedBall (by simp [sourceAnnularBump])

theorem sourceAnnularBump_norm_bounds {z : ℂ} (hz : z ∈ tsupport sourceAnnularBump) :
    3 / 4 ≤ ‖z‖ ∧ ‖z‖ ≤ 5 / 4 := by
  rw [sourceAnnularBump.tsupport_eq, Metric.mem_closedBall, dist_eq_norm] at hz
  change ‖z - 1‖ ≤ 1 / 4 at hz
  have hl := norm_sub_norm_le (1 : ℂ) z
  have hu := norm_sub_norm_le z (1 : ℂ)
  rw [norm_sub_rev] at hl
  simp only [norm_one] at hl hu
  constructor <;> linarith

theorem sourceAnnularBump_integrable : Integrable sourceAnnularBump :=
  sourceAnnularBump.continuous.integrable_of_hasCompactSupport sourceAnnularBump_compact

theorem sourceAnnularBump_integral_pos : 0 < ∫ z : ℂ, sourceAnnularBump z :=
  integral_pos_of_integrable_nonneg_nonzero sourceAnnularBump.continuous
    sourceAnnularBump_integrable sourceAnnularBump_nonneg (by rw [sourceAnnularBump_one]; norm_num)

def sourceAnnularWeightedBump (z : ℂ) : ℝ :=
  sourceAnnularBump z * ‖z‖ ^ (-(1 / 3 : ℝ))

theorem sourceAnnularWeightedBump_regularized (z : ℂ) :
    sourceAnnularWeightedBump z =
      sourceAnnularBump z * (max (1 / 4 : ℝ) ‖z‖) ^ (-(1 / 3 : ℝ)) := by
  by_cases hz : sourceAnnularBump z = 0
  · simp [sourceAnnularWeightedBump, hz]
  · have hb := (sourceAnnularBump_norm_bounds (subset_tsupport _ hz)).1
    rw [max_eq_right (by linarith : (1 / 4 : ℝ) ≤ ‖z‖)]
    rfl

theorem sourceAnnularWeightedBump_continuous : Continuous sourceAnnularWeightedBump := by
  have hp : Continuous (fun z : ℂ => (max (1 / 4 : ℝ) ‖z‖) ^ (-(1 / 3 : ℝ))) := by
    apply Continuous.rpow_const (by fun_prop)
    intro z
    left
    have h : (1 / 4 : ℝ) ≤ max (1 / 4 : ℝ) ‖z‖ := le_max_left _ _
    linarith
  exact (sourceAnnularBump.continuous.mul hp).congr fun z =>
    (sourceAnnularWeightedBump_regularized z).symm

theorem sourceAnnularWeightedBump_compact : HasCompactSupport sourceAnnularWeightedBump :=
  sourceAnnularBump_compact.mul_right

theorem sourceAnnularWeightedBump_integrable : Integrable sourceAnnularWeightedBump :=
  sourceAnnularWeightedBump_continuous.integrable_of_hasCompactSupport
    sourceAnnularWeightedBump_compact

theorem sourceAnnularWeightedBump_integral_pos :
    0 < ∫ z : ℂ, sourceAnnularWeightedBump z := by
  apply integral_pos_of_integrable_nonneg_nonzero sourceAnnularWeightedBump_continuous
    sourceAnnularWeightedBump_integrable
    (fun z => mul_nonneg (sourceAnnularBump_nonneg z) (Real.rpow_nonneg (norm_nonneg z) _))
    (x := (1 : ℂ))
  simp [sourceAnnularWeightedBump, sourceAnnularBump_one]

end
end ArtinMatthews.VaryingKummerAnalytic
