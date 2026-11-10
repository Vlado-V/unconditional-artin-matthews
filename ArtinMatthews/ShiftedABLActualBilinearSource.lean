module

public import ArtinMatthews.CubicReciprocityNonprincipalCharacterBase
public import ArtinMatthews.GiantSamplingShiftedInput
public import ArtinMatthews.ShiftedABLActualCorrelationSource
public import ArtinMatthews.ShiftedBilinearSource
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The native cubic numerator satisfies the original full shifted
bilinear bound, with the level-prime reduction supplied by the receiver. -/

namespace ArtinMatthews

open Set
open scoped ContDiff

theorem cubicNumerator_shiftedBilinearBound
    (a : ℤ) (ha : a ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y^3=(a : OAI.CubicFirstMoment.Eisenstein))
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ)
    (hsupp : Function.support Φ ⊆ Icc (1 : ℝ) 2) :
    ∀ ν : ℝ, 0 < ν → ∃ Cν : ℝ, 0 < Cν ∧ ∀ x : ℝ, 1 ≤ x →
      GiantSamplingShiftedBilinearBound (cubicNumeratorHeckeCharacter a ha) Φ x ν Cν :=
  cubicNumerator_shiftedBilinearBound_of_correlation a ha
    (cubicNumerator_shiftedABLCorrelationSource a ha hnoncube) Φ hΦ hsupp

end ArtinMatthews
