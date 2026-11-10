module

public import ArtinMatthews.CubicReciprocityNonprincipalCharacterBase
public import ArtinMatthews.CubicReciprocityNonprincipalConjugationModel
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
public import OAI.NumberTheory.CubicGram.Reciprocity


set_option backward.privateInPublic true
@[expose] public section

/-! The actual cubic Hecke characters are anti-invariant under complex
conjugation of their rational residue modulus. -/

noncomputable section

namespace ArtinMatthews

open OAI OAI.SevenEighths OAI.CubicFirstMoment

local notation "EO" => HeckeFamily.O

theorem cubicNumeratorLift_conjugate_int (A : ℤ) (x : Eisenstein) :
    cubicNumeratorLift (A : Eisenstein) (conjugate x) =
      star (cubicNumeratorLift (A : Eisenstein) x) := by
  have hunit : IsUnit (Ideal.Quotient.mk (modulus 3) (conjugate x)) ↔
      IsUnit (Ideal.Quotient.mk (modulus 3) x) := by
    have h3 : conjugate (3 : Eisenstein) = 3 := map_ofNat conjugate 3
    have h := isUnit_residue_conjugate (p := (3 : Eisenstein)) (v := x)
    rw [h3] at h
    exact h
  by_cases hx : IsUnit (Ideal.Quotient.mk (modulus 3) x)
  · rw [cubicNumeratorLift, ite_eq_left (hunit.mpr hx), cubicNumeratorLift, ite_eq_left hx,
      primaryNormalize_conjugate]
    simpa only [map_intCast] using
      cubicSymbol_conjugate (primaryNormalize_primary hx) (A : Eisenstein)
  · simp only [cubicNumeratorLift, ite_eq_right hx, ite_eq_right (mt hunit.mp hx), star_zero]

/-- Anti-conjugation on every residue class, including the nonunits where
the character is zero. -/
theorem cubicNumeratorHeckeResidue_conjugate (A : ℤ) (hA : A ≠ 0)
    (x : EO ⧸ cubicNumeratorHeckeModulus A) :
    cubicNumeratorHeckeResidue A hA (cubicNumeratorResidueConjugation A x) =
      star (cubicNumeratorHeckeResidue A hA x) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  change cubicNumeratorChar cubicSupplementaryPeriodicity_proved (A : Eisenstein)
      (by exact_mod_cast hA)
      (Ideal.Quotient.mk (modulus (9 * (A : Eisenstein)))
        (heckeIntegersEquivCubicEisenstein (heckeIntegerConjugation y))) =
    star (cubicNumeratorChar cubicSupplementaryPeriodicity_proved (A : Eisenstein)
      (by exact_mod_cast hA)
      (Ideal.Quotient.mk (modulus (9 * (A : Eisenstein)))
        (heckeIntegersEquivCubicEisenstein y)))
  rw [heckeIntegerConjugation_model, cubicNumeratorChar_mk, cubicNumeratorChar_mk]
  exact cubicNumeratorLift_conjugate_int A _

theorem cubicNumeratorHeckeCharacter_residue_conjugate (A : ℤ) (hA : A ≠ 0)
    (x : EO ⧸ cubicNumeratorHeckeModulus A) :
    (cubicNumeratorHeckeCharacter A hA).residue (cubicNumeratorResidueConjugation A x) =
      star ((cubicNumeratorHeckeCharacter A hA).residue x) :=
  cubicNumeratorHeckeResidue_conjugate A hA x

/-- Equivalently, conjugation inverts the value of the actual finite
cubic Hecke character. -/
theorem cubicNumeratorHeckeCharacter_residue_conjugate_inv (A : ℤ) (hA : A ≠ 0)
    (x : EO ⧸ cubicNumeratorHeckeModulus A) :
    (cubicNumeratorHeckeCharacter A hA).residue (cubicNumeratorResidueConjugation A x) =
      ((cubicNumeratorHeckeCharacter A hA).residue x)⁻¹ := by
  let : Finite (EO ⧸ cubicNumeratorHeckeModulus A) :=
    Ring.HasFiniteQuotients.finiteQuotient (cubicNumeratorHeckeModulus_ne_bot hA)
  have h := cubicNumeratorHeckeResidue_conjugate A hA x
  rw [MulChar.star_apply', MulChar.inv_apply_eq_inv'] at h
  exact h

theorem cubicNumeratorHeckeCharacter_element_conjugate (A : ℤ) (hA : A ≠ 0)
    (x : EO) :
    HeckeFamily.elementCoeff (cubicNumeratorHeckeCharacter A hA)
        (heckeIntegerConjugation x) =
      star (HeckeFamily.elementCoeff (cubicNumeratorHeckeCharacter A hA) x) :=
  cubicNumeratorHeckeCharacter_residue_conjugate A hA
    (Ideal.Quotient.mk (cubicNumeratorHeckeModulus A) x)

end ArtinMatthews
