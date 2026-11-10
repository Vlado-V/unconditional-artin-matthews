module

public import ArtinMatthews.CubicReciprocityNonprincipalConductor
public import ArtinMatthews.CubicReciprocityNonprincipalTransport
public import OAI.NumberTheory.CubicMoment.Estimates.CubicSupplementaryPeriodicityProof
public import ArtinMatthews.CubicReciprocityNonprincipalModel
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
public import Mathlib.Topology.Sheaves.Init
public import OAI.NumberTheory.CubicMoment.Estimates.CubicNumeratorOrder


set_option backward.privateInPublic true
@[expose] public section

/-!
# A nonprincipal finite-conductor cubic Hecke character

The full cubic numerator character includes the unit and ramified
supplementary factors. It therefore handles radicands supported at `2` or
`3` as well as the ordinary prime factors. Transport gives an actual
`HeckeFamily.Character`, with modulus `(9A)` and no assumed nonprincipality.
-/

noncomputable section

namespace ArtinMatthews

open OAI OAI.SevenEighths OAI.CubicFirstMoment

local notation "EO" => HeckeFamily.O

/-- Actual quotient-ring transport of the full numerator modulus. -/
def cubicNumeratorResidueEquiv (A : ℤ) :
    EO ⧸ cubicNumeratorHeckeModulus A ≃+* Residues (9 * (A : Eisenstein)) :=
  Ideal.quotientEquiv (cubicNumeratorHeckeModulus A) (modulus (9 * (A : Eisenstein)))
    heckeIntegersEquivCubicEisenstein (by
      simp only [cubicNumeratorHeckeModulus, modulus, Ideal.map_span, Set.image_singleton,
        map_mul, map_ofNat, map_intCast])

/-- The transported finite cubic residue character. -/
def cubicNumeratorHeckeResidue (A : ℤ) (hA : A ≠ 0) :
    MulChar (EO ⧸ cubicNumeratorHeckeModulus A) ℂ :=
  residueCharacterPullback (cubicNumeratorResidueEquiv A)
    (cubicNumeratorChar cubicSupplementaryPeriodicity_proved (A : Eisenstein)
      (by exact_mod_cast hA))

theorem cubicNumeratorHeckeResidue_unit (A : ℤ) (hA : A ≠ 0) (u : EOˣ) :
    cubicNumeratorHeckeResidue A hA
      (Ideal.Quotient.mk (cubicNumeratorHeckeModulus A) (u : EO)) = 1 := by
  change cubicNumeratorChar cubicSupplementaryPeriodicity_proved (A : Eisenstein)
    (by exact_mod_cast hA)
    (Ideal.Quotient.mk (modulus (9 * (A : Eisenstein)))
      (heckeIntegersEquivCubicEisenstein (u : EO))) = 1
  exact cubicNumeratorChar_units cubicSupplementaryPeriodicity_proved (A : Eisenstein)
    (by exact_mod_cast hA)
    (Units.map heckeIntegersEquivCubicEisenstein.toMonoidHom u)

theorem cubicNumeratorHeckeResidue_cube (A : ℤ) (hA : A ≠ 0) :
    cubicNumeratorHeckeResidue A hA ^ 3 = 1 := by
  rw [cubicNumeratorHeckeResidue, residueCharacterPullback_pow, cubicNumeratorChar_cube,
    residueCharacterPullback_one]

/-- The genuine finite-conductor Hecke character. -/
def cubicNumeratorHeckeCharacter (A : ℤ) (hA : A ≠ 0) : HeckeFamily.Character :=
  HeckeFamily.Character.ofResidue (cubicNumeratorHeckeModulus A)
    (cubicNumeratorHeckeModulus_ne_bot hA) (cubicNumeratorHeckeResidue A hA)
    (cubicNumeratorHeckeResidue_unit A hA)

@[simp] theorem cubicNumeratorHeckeCharacter_modulus (A : ℤ) (hA : A ≠ 0) :
    (cubicNumeratorHeckeCharacter A hA).modulus = Ideal.span {9 * (A : EO)} := rfl

@[simp] theorem cubicNumeratorHeckeCharacter_modulus_absNorm (A : ℤ) (hA : A ≠ 0) :
    (cubicNumeratorHeckeCharacter A hA).modulus.absNorm = 81 * A.natAbs ^ 2 :=
  cubicNumeratorHeckeModulus_absNorm A

/-- The literal two-coordinate period used by the Hecke analytic family is
also explicit. -/
@[simp] theorem cubicNumeratorHeckeCharacter_period (A : ℤ) (hA : A ≠ 0) :
    (cubicNumeratorHeckeCharacter A hA).period = 81 * A.natAbs ^ 2 := by
  let : Finite (EO ⧸ cubicNumeratorHeckeModulus A) :=
    Ring.HasFiniteQuotients.finiteQuotient (cubicNumeratorHeckeModulus_ne_bot hA)
  let : Fintype (EO ⧸ cubicNumeratorHeckeModulus A) := Fintype.ofFinite _
  change Fintype.card (EO ⧸ cubicNumeratorHeckeModulus A) = _
  rw [← Nat.card_eq_fintype_card]
  exact cubicNumeratorHeckeModulus_absNorm A

theorem cubicNumeratorHeckeCharacter_element_primary (A : ℤ) (hA : A ≠ 0)
    (x : EO) (hx : primary (heckeIntegersEquivCubicEisenstein x)) :
    HeckeFamily.elementCoeff (cubicNumeratorHeckeCharacter A hA) x =
      cubicSymbol (heckeIntegersEquivCubicEisenstein x) (A : Eisenstein) := by
  exact cubicNumeratorChar_primary cubicSupplementaryPeriodicity_proved
    (A : Eisenstein) (by exact_mod_cast hA) hx

/-- The residue character has cubic order, including its zero values away
from the unit group. -/
theorem cubicNumeratorHeckeCharacter_cube (A : ℤ) (hA : A ≠ 0) :
    (cubicNumeratorHeckeCharacter A hA).residue ^ 3 = 1 :=
  cubicNumeratorHeckeResidue_cube A hA

end ArtinMatthews
