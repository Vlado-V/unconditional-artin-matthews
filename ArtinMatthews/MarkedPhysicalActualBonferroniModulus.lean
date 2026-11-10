module

public import ArtinMatthews.MarkedPhysicalBonferroniModulus
public import ArtinMatthews.MarkedPhysicalPathArrays
public import ArtinMatthews.MarkedPhysicalActualUsedBudget
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

/-! The performed modulus at the actual moment/pad lengths satisfies the
proved root-count ceiling with the used-prime budget fully discharged. -/

noncomputable section
namespace ArtinMatthews

theorem markedPhysicalActualBonferroniModulus_bound
    {J : Type*} [Fintype J] (e : J → ℝ) {x : ℝ}
    (hlog : 1 ≤ Real.log x) (he : ∀ j,e j ≤ (1/5:ℝ))
    (a : MarkedPhysicalLabelPath (fun j => markedLogPowerBand (e j) x)
      (markedPadSlots x) (markedMemoryMomentLength x))
    (T : Finset ℕ)
    (hT : T ⊆ markedPhysicalBandPrimes (fun j => markedLogPowerBand (e j) x) \ markedPhysicalPathUsedPrimes Finset.univ a)
    (hc : T.card ≤ 2*markedPhysicalBonferroniDepth x+1) :
    (markedPhysicalBonferroniModulus Finset.univ a T:ℝ) ≤
      Real.exp ((16*(Fintype.card J:ℝ)+10)*(Real.log x)^(49/50:ℝ)) :=
  markedPhysicalBonferroniModulus_actual_bound e (by positivity) hlog he (by norm_num) Finset.univ a hT hc
    (markedPhysicalActualUsedProduct_bound e hlog he a)

end ArtinMatthews
