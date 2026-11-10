module

public import ArtinMatthews.CubicReciprocityNonprincipalCharacterBase
public import ArtinMatthews.CubicTheta
public import ArtinMatthews.ShiftedVoronoiCharacter
public import ArtinMatthews.CubicThetaActualTransformation
public import ArtinMatthews.CubicThetaConstructedWeil
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

/-! The actual cubic Hecke theta congruence law, specialized to the proved
real, finite, and adelic Weil construction. No representation is a hypothesis. -/
noncomputable section
namespace ArtinMatthews

open scoped MatrixGroups
open Complex UpperHalfPlane

/-- The exact transformation at the compatible level `6 M²`, using the
genuinely constructed Weil representation rather than assumed covariance. -/
theorem cubicNumeratorHeckeTheta_constructed_transform
    (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y ^ 3 = (A : OAI.CubicFirstMoment.Eisenstein))
    (M : ℕ) [NeZero M] (heven : 2 ∣ M) (hdiv : 9 * A ∣ (M : ℤ))
    (γ : SL(2, ℤ)) (hc : 6 * (M : ℤ) ^ 2 ∣ γ 1 0) (τ : ℍ) :
    heckeTheta (cubicNumeratorHeckeCharacter A hA) (γ • τ) =
      cubicThetaNebentypus (γ 1 1) * ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) *
        heckeTheta (cubicNumeratorHeckeCharacter A hA) τ :=
  cubicNumeratorHeckeTheta_transform cubicThetaWeilData A hA hnoncube M heven hdiv γ hc τ

end ArtinMatthews
