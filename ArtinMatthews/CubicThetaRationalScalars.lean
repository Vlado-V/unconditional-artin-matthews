module

public import ArtinMatthews.CubicReciprocityNonprincipalConjugation


set_option backward.privateInPublic true
@[expose] public section

/-! The actual anticyclotomic cubic character is trivial on invertible
rational scalars, as required by its scalar congruence transformation. -/
noncomputable section
namespace ArtinMatthews

open OAI OAI.SevenEighths
local notation "EO" => HeckeFamily.O

/-- A fixed point of conjugation has trivial nonzero cubic character value. -/
theorem cubicNumeratorHeckeCharacter_residue_fixed (A : ℤ) (hA : A ≠ 0)
    (x : EO ⧸ cubicNumeratorHeckeModulus A) (hx : IsUnit x)
    (hfixed : cubicNumeratorResidueConjugation A x = x) :
    (cubicNumeratorHeckeCharacter A hA).residue x = 1 := by
  let z := cubicNumeratorHeckeResidue A hA x
  have h3 : z ^ 3 = 1 := by
    have h := congrArg (fun χ : MulChar (EO ⧸ cubicNumeratorHeckeModulus A) ℂ => χ x)
      (cubicNumeratorHeckeResidue_cube A hA)
    simpa only [MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), MulChar.one_apply hx]
      using h
  have hz : z ≠ 0 := by
    intro hz
    simp [hz] at h3
  have hinv : z = z⁻¹ := by
    have h := cubicNumeratorHeckeCharacter_residue_conjugate_inv A hA x
    change cubicNumeratorHeckeResidue A hA (cubicNumeratorResidueConjugation A x) =
      (cubicNumeratorHeckeResidue A hA x)⁻¹ at h
    rw [hfixed] at h
    exact h
  have h2 : z ^ 2 = 1 := by
    calc
      z ^ 2 = z * z := pow_two z
      _ = z * z⁻¹ := congrArg (fun t : ℂ => z * t) hinv
      _ = 1 := mul_inv_cancel₀ hz
  change z = 1
  simpa only [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, h2, one_mul] using h3

/-- Rational residue units are fixed by conjugation, hence have value one. -/
theorem cubicNumeratorHeckeCharacter_residue_int (A : ℤ) (hA : A ≠ 0)
    (d : ℤ) (hd : IsUnit (d : EO ⧸ cubicNumeratorHeckeModulus A)) :
    (cubicNumeratorHeckeCharacter A hA).residue (d : EO ⧸ cubicNumeratorHeckeModulus A) =
      1 :=
  cubicNumeratorHeckeCharacter_residue_fixed A hA _ hd (map_intCast _ d)

/-- Multiplication by an invertible rational scalar preserves every residue
weight, including zero weights. -/
theorem cubicNumeratorHeckeCharacter_residue_int_mul (A : ℤ) (hA : A ≠ 0)
    (d : ℤ) (hd : IsUnit (d : EO ⧸ cubicNumeratorHeckeModulus A))
    (x : EO ⧸ cubicNumeratorHeckeModulus A) :
    (cubicNumeratorHeckeCharacter A hA).residue ((d : EO ⧸ cubicNumeratorHeckeModulus A) * x) =
      (cubicNumeratorHeckeCharacter A hA).residue x := by
  change cubicNumeratorHeckeResidue A hA ((d : EO ⧸ cubicNumeratorHeckeModulus A) * x) = _
  rw [map_mul]
  exact (congrArg (fun z : ℂ => z * cubicNumeratorHeckeResidue A hA x)
    (cubicNumeratorHeckeCharacter_residue_int A hA d hd)).trans (one_mul _)

/-- The same invariance holds for the actual integral theta coefficient. -/
theorem cubicNumeratorHeckeCharacter_element_int_mul (A : ℤ) (hA : A ≠ 0)
    (d : ℤ) (hd : IsUnit (d : EO ⧸ cubicNumeratorHeckeModulus A)) (x : EO) :
    HeckeFamily.elementCoeff (cubicNumeratorHeckeCharacter A hA) ((d : EO) * x) =
      HeckeFamily.elementCoeff (cubicNumeratorHeckeCharacter A hA) x := by
  unfold HeckeFamily.elementCoeff
  rw [map_mul, map_intCast]
  exact cubicNumeratorHeckeCharacter_residue_int_mul A hA d hd _

end ArtinMatthews
