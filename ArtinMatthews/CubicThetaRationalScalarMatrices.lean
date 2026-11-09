module

public import ArtinMatthews.CubicThetaRationalScalars
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup


set_option backward.privateInPublic true
@[expose] public section

/-! Rational diagonal scalars supplied by determinant-one congruence matrices. -/
noncomputable section
namespace ArtinMatthews

open OAI OAI.SevenEighths
open scoped MatrixGroups
local notation "EO" => HeckeFamily.O

/-- The lower-right entry of a determinant-one matrix is invertible modulo
`(9A)` whenever its lower-left entry is divisible by `9A`. -/
theorem cubicTheta_lowerRight_isUnit (A : ℤ) (γ : SL(2, ℤ))
    (hc : 9 * A ∣ γ 1 0) :
    IsUnit (γ 1 1 : EO ⧸ cubicNumeratorHeckeModulus A) := by
  have hc0 : (γ 1 0 : EO ⧸ cubicNumeratorHeckeModulus A) = 0 := by
    change Ideal.Quotient.mk (cubicNumeratorHeckeModulus A) (γ 1 0 : EO) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply Ideal.mem_span_singleton.mpr
    obtain ⟨k, hk⟩ := hc
    exact ⟨(k : EO), by exact_mod_cast hk⟩
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using γ.det_coe
  have hd : (γ 0 0 : EO ⧸ cubicNumeratorHeckeModulus A) *
      (γ 1 1 : EO ⧸ cubicNumeratorHeckeModulus A) = 1 := by
    have h := congrArg (Int.castRingHom (EO ⧸ cubicNumeratorHeckeModulus A)) hdet
    simpa only [Int.coe_castRingHom, Int.cast_sub, Int.cast_mul, Int.cast_one,
      hc0, mul_zero, sub_zero] using h
  exact IsUnit.of_mul_eq_one_right _ hd

/-- The actual rational-scalar eigenvalue is one for the congruence matrices
in the intended weight-one transformation law. -/
theorem cubicTheta_lowerRight_character_eq_one (A : ℤ) (hA : A ≠ 0)
    (γ : SL(2, ℤ)) (hc : 9 * A ∣ γ 1 0) :
    (cubicNumeratorHeckeCharacter A hA).residue
      (γ 1 1 : EO ⧸ cubicNumeratorHeckeModulus A) = 1 :=
  cubicNumeratorHeckeCharacter_residue_int A hA _ (cubicTheta_lowerRight_isUnit A γ hc)

end ArtinMatthews
