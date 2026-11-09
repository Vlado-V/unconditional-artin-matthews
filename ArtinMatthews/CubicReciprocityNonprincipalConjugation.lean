module

public import ArtinMatthews.CubicReciprocityNonprincipalCharacterBase
public import ArtinMatthews.CubicReciprocityNonprincipalConjugationModel


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
