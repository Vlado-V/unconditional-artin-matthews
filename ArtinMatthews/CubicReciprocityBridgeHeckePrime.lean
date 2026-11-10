module

public import ArtinMatthews.CubicReciprocityNonprincipalCharacterBase
public import ArtinMatthews.CubicThetaCoefficients
public import ArtinMatthews.CubicReciprocityBridgePrimary
public import ArtinMatthews.CubicReciprocityBridgeSymbol
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

/-! Exact prime values of the actual finite-conductor cubic numerator character. -/

noncomputable section
namespace ArtinMatthews
open OAI OAI.ActualEisensteinCubic OAI.SevenEighths
local notation "EO" => HeckeFamily.O

/-- At a prime away from `3A`, the actual numerator Hecke character has the
same value as the actual finite-field cubic residue character. -/
theorem cubicNumeratorHeckeCharacter_prime (A : ℤ) (hA : A ≠ 0)
    (P : Ideal EO) [P.IsMaximal] (hg : lambda ∉ P) (hAP : (A : EO) ∉ P) :
    thetaIdealCharacter (cubicNumeratorHeckeCharacter A hA) P =
      ConcreteTraceCRT.eisEmbedding (cubicChar P hg (Ideal.Quotient.mk P (A : EO))) := by
  obtain ⟨p, hP, hp0, hprimary⟩ := exists_cubicMoment_primary_generator P hg
  have hp : Prime p := (Ideal.span_singleton_prime hp0).mp (hP ▸ inferInstance)
  have hpE : CubicFirstMoment.primaryPrime (heckeIntegersEquivCubicEisenstein p) :=
    ⟨hprimary, (MulEquiv.prime_iff heckeIntegersEquivCubicEisenstein).mpr hp⟩
  calc
    thetaIdealCharacter (cubicNumeratorHeckeCharacter A hA) P =
        thetaIdealCharacter (cubicNumeratorHeckeCharacter A hA) (Ideal.span {p}) :=
      congrArg _ hP
    _ = HeckeFamily.elementCoeff (cubicNumeratorHeckeCharacter A hA) p :=
      thetaIdealCharacter_span _ hp0
    _ = CubicFirstMoment.cubicSymbol (heckeIntegersEquivCubicEisenstein p)
        (A : CubicFirstMoment.Eisenstein) :=
      cubicNumeratorHeckeCharacter_element_primary A hA p hprimary
    _ = ConcreteTraceCRT.eisEmbedding (cubicChar P hg (Ideal.Quotient.mk P (A : EO))) := by
      simpa only [map_intCast] using cubicSymbol_eq_actualCubicChar P hg hP hpE hAP

end ArtinMatthews
