module

public import ArtinMatthews.CubicReciprocityNonprincipalCharacterBase
public import OAI.NumberTheory.CubicMoment.Estimates.CubicNumeratorNoncube


set_option backward.privateInPublic true
@[expose] public section

/-! Exact nonprincipality of the actual cubic Fourier Hecke characters. -/

noncomputable section
namespace ArtinMatthews
open OAI OAI.SevenEighths OAI.CubicFirstMoment
local notation "EO" => HeckeFamily.O

/-- Exact principality criterion for the transported arithmetic character. -/
theorem cubicNumeratorHeckeCharacter_principal_iff (A : ℤ) (hA : A ≠ 0) :
    (cubicNumeratorHeckeCharacter A hA).residue = 1 ↔
      ∃ y : Eisenstein, y ^ 3 = (A : Eisenstein) := by
  exact (residueCharacterPullback_eq_one_iff (cubicNumeratorResidueEquiv A)
    (cubicNumeratorChar cubicSupplementaryPeriodicity_proved (A : Eisenstein)
      (by exact_mod_cast hA))).trans
    (cubicNumeratorChar_eq_one_iff_cube cubicSupplementaryPeriodicity_proved
      (by exact_mod_cast hA))

/-- Full noncube numerators give nonprincipal actual Hecke residue characters. -/
theorem cubicNumeratorHeckeCharacter_nonprincipal (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : Eisenstein, y ^ 3 = (A : Eisenstein)) :
    (cubicNumeratorHeckeCharacter A hA).residue ≠ 1 := by
  exact residueCharacterPullback_ne_one (cubicNumeratorResidueEquiv A)
    (cubicNumeratorChar_noncube cubicSupplementaryPeriodicity_proved
      (by exact_mod_cast hA) hnoncube)

/-- In particular, a nontrivial Fourier term cannot yield a quadratic
exceptional character. -/
theorem cubicNumeratorHeckeCharacter_square_nonprincipal (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : Eisenstein, y ^ 3 = (A : Eisenstein)) :
    (cubicNumeratorHeckeCharacter A hA).residue ^ 2 ≠ 1 := by
  intro htwo
  apply cubicNumeratorHeckeCharacter_nonprincipal A hA hnoncube
  calc
    (cubicNumeratorHeckeCharacter A hA).residue =
        (cubicNumeratorHeckeCharacter A hA).residue ^ 2 *
          (cubicNumeratorHeckeCharacter A hA).residue := by rw [htwo, one_mul]
    _ = (cubicNumeratorHeckeCharacter A hA).residue ^ 3 := (pow_succ _ 2).symm
    _ = 1 := cubicNumeratorHeckeCharacter_cube A hA

/-- The nonprincipality needed for each nonconstant term in the actual
Fourier expansion follows from the original Fourier character itself. -/
theorem cubicNumeratorHeckeCharacter_nonprincipal_of_fourier {S : Finset ℤ}
    (χ : AddChar (Additive (integerCubicGaloisGroup S)) ℂ) (hχ : χ ≠ 0)
    {A : ℤ} (hA : A ≠ 0) {R : integerCubicField S} (hR0 : R ≠ 0)
    (hR : R ^ 3 = (A : integerCubicField S))
    (hrep : ∀ σ : integerCubicGaloisGroup S,
      χ (Additive.ofMul σ) = ((σ.val R / R : integerCubicField S) : ℂ)) :
    (cubicNumeratorHeckeCharacter A hA).residue ≠ 1 :=
  cubicNumeratorHeckeCharacter_nonprincipal A hA
    (cubicFourier_radical_not_cube_in_cubicMoment χ hχ hR0 hR hrep)

/-- Every nonconstant Fourier term of the actual cubic Galois group yields
an actual nonprincipal Hecke character. Its defining radical, finite modulus
and values on primary generators are all retained in the conclusion. -/
theorem exists_cubicFourier_nonprincipal_heckeCharacter {S : Finset ℤ}
    (hzero : ∀ a ∈ S, a ≠ 0)
    (χ : AddChar (Additive (integerCubicGaloisGroup S)) ℂ) (hχ : χ ≠ 0) :
    ∃ (A : ℤ) (R : integerCubicField S) (ψ : HeckeFamily.Character),
      A ≠ 0 ∧ R ≠ 0 ∧ R ^ 3 = (A : integerCubicField S) ∧
      (∀ σ : integerCubicGaloisGroup S,
        χ (Additive.ofMul σ) = ((σ.val R / R : integerCubicField S) : ℂ)) ∧
      ψ.residue ≠ 1 ∧ ψ.modulus = Ideal.span {9 * (A : EO)} ∧
      ψ.modulus.absNorm = 81 * A.natAbs ^ 2 ∧
      ∀ x : EO, primary (heckeIntegersEquivCubicEisenstein x) →
        HeckeFamily.elementCoeff ψ x =
          cubicSymbol (heckeIntegersEquivCubicEisenstein x) (A : Eisenstein) := by
  obtain ⟨e, R, hR0, hR, hrep⟩ := cubicFourier_character_has_radical hzero χ
  let A : ℤ := cubicProductRadicand (fun i => (e i : ℕ))
  have hA : A ≠ 0 := by
    intro hA
    have hz : R ^ 3 = (A : integerCubicField S) := hR
    rw [hA, Int.cast_zero] at hz
    exact pow_ne_zero 3 hR0 hz
  refine ⟨A, R, cubicNumeratorHeckeCharacter A hA, hA, hR0, hR, hrep, ?_, rfl,
    cubicNumeratorHeckeModulus_absNorm A, ?_⟩
  · exact cubicNumeratorHeckeCharacter_nonprincipal_of_fourier χ hχ hA hR0 hR hrep
  · exact cubicNumeratorHeckeCharacter_element_primary A hA

end ArtinMatthews
