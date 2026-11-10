module

public import ArtinMatthews.MarkedPhysicalCoordinateIndex
public import ArtinMatthews.MarkedPhysicalCoordinateTubeBudget
public import ArtinMatthews.MarkedMemoryOrphanParameterBounds
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual ordered markings, relative coordinates and both permutation
copies cost exp(C*log(x)) at the original source hierarchy. Invalid
physical arrays are only overcounted, never identified or quotiented. -/
namespace ArtinMatthews
noncomputable section

def markedPhysicalCoordinateIndexCost (groups : ℕ) (K A : ℝ) : ℝ :=
  markedPhysicalCoordinateTubeCost K A+48*(groups:ℝ)

theorem markedPhysicalCoordinateIndexCost_nonneg (groups : ℕ) {K A : ℝ}
    (hK : 0 ≤ K) (hA : 0 ≤ A) : 0 ≤ markedPhysicalCoordinateIndexCost groups K A := by
  unfold markedPhysicalCoordinateIndexCost markedPhysicalCoordinateTubeCost
  positivity

theorem markedPhysicalLabelPath_exponent_bound (groups : ℕ) {x : ℝ} (hlog : 1 ≤ Real.log x) :
    2*(groups:ℝ)*(markedPadSlots x:ℝ)*((markedMemoryMomentLength x:ℝ)+1)*(Real.log x)^(1/5:ℝ) ≤
      16*(groups:ℝ)*Real.log x := by
  have hL : 0 < Real.log x := by linarith
  have ha := markedMemoryActiveOccurrences_rpow_bound groups hlog
  push_cast at ha
  have hm := mul_le_mul_of_nonneg_right ha
    (show 0 ≤ 2*(Real.log x)^(1/5:ℝ) by positivity)
  have he : (Real.log x)^(3/4:ℝ)*(Real.log x)^(1/5:ℝ)=(Real.log x)^(19/20:ℝ) := by
    rw [← Real.rpow_add hL]
    norm_num
  have hp : (Real.log x)^(19/20:ℝ) ≤ Real.log x := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hlog (by norm_num : (19/20:ℝ) ≤ 1)
  have hg := mul_le_mul_of_nonneg_left hp (show 0 ≤ 16*(groups:ℝ) by positivity)
  nlinarith

theorem markedPhysicalCopyPath_exponent_bound (groups : ℕ) {x : ℝ} (hlog : 1 ≤ Real.log x) :
    2*(groups:ℝ)*(markedPadSlots x:ℝ)^2*(markedMemoryMomentLength x:ℝ) ≤
      32*(groups:ℝ)*Real.log x := by
  have hL : 0 < Real.log x := by linarith
  have hM := markedPadSlots_pow_le 2 hlog
  norm_num only [Nat.cast_ofNat] at hM
  have hN := (markedMemoryMomentLength_sqrt_bound hlog).1
  have hn : (markedMemoryMomentLength x:ℝ) ≤ 4*(Real.log x)^(1/2:ℝ) := by linarith
  have hm := mul_le_mul hM hn (Nat.cast_nonneg _) (by positivity)
  have he : (Real.log x)^(2/100:ℝ)*(Real.log x)^(1/2:ℝ)=(Real.log x)^(13/25:ℝ) := by
    rw [← Real.rpow_add hL]
    norm_num
  have hp : (Real.log x)^(13/25:ℝ) ≤ Real.log x := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hlog (by norm_num : (13/25:ℝ) ≤ 1)
  have hprod : (markedPadSlots x:ℝ)^2*(markedMemoryMomentLength x:ℝ) ≤ 16*Real.log x := by
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 2*(groups:ℝ) by positivity)
  nlinarith

theorem markedPhysicalCoordinateIndex_actual_card_bound
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ)
    {x K H A : ℝ} (hlog : 1 ≤ Real.log x) (he : ∀ j,e j ≤ (1/5:ℝ))
    (hK : 0 ≤ K) (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hHhi : H ≤ Real.exp (A*(Real.log x)^(21/100:ℝ))) :
    (Fintype.card (MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
      (markedPadSlots x) (markedMemoryMomentLength x)
      (markedPhysicalMomentTubeRadius (markedMemoryMomentLength x) K H)):ℝ) ≤
      Real.exp (markedPhysicalCoordinateIndexCost (Fintype.card J) K A*Real.log x) := by
  have hc := markedPhysicalCoordinateIndex_card_exp_bound e hlog he (markedPadSlots x)
    (markedMemoryMomentLength x) (markedPhysicalMomentTubeRadius (markedMemoryMomentLength x) K H)
  have hl := Real.exp_le_exp.mpr (markedPhysicalLabelPath_exponent_bound (Fintype.card J) hlog)
  have ht := markedPhysicalMomentTube_path_budget hlog hK hH hA hHhi
  have hs := Real.exp_le_exp.mpr (markedPhysicalCopyPath_exponent_bound (Fintype.card J) hlog)
  apply hc.trans
  calc
    _ ≤ Real.exp (16*(Fintype.card J:ℝ)*Real.log x)*
        Real.exp (markedPhysicalCoordinateTubeCost K A*Real.log x)*
        Real.exp (32*(Fintype.card J:ℝ)*Real.log x) :=
      mul_le_mul (mul_le_mul hl ht (by positivity) (Real.exp_nonneg _)) hs (Real.exp_nonneg _) (by positivity)
    _ = _ := by
      rw [← Real.exp_add,← Real.exp_add]
      congr 1
      unfold markedPhysicalCoordinateIndexCost
      ring

end
end ArtinMatthews
