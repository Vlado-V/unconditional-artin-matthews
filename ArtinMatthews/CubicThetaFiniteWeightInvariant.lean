module

public import ArtinMatthews.CubicThetaAdelicIdentity
public import ArtinMatthews.CubicThetaRationalScalarMatrices
public import ArtinMatthews.CubicThetaResidueReduction
public import ArtinMatthews.CubicThetaActualCusps


set_option backward.privateInPublic true
@[expose] public section

/-! The actual cubic numerator weights are invariant under the finite scalar
permutation attached to a determinant-one congruence matrix. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators MatrixGroups
open OAI OAI.SevenEighths UpperHalfPlane
open OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData
open OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction
open OAI.AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM
local notation "EO" => HeckeFamily.O

/-- Coordinate reduction is compatible with multiplication by rational integers. -/
theorem cubicThetaCoordinateHom_int_mul (M : ℕ) (d : ℤ) (x y : ZMod M) :
    cubicThetaCoordinateHom M ((d : ZMod M) * x, (d : ZMod M) * y) =
      (d : CubicThetaResidue M) * cubicThetaCoordinateHom M (x, y) := by
  have hi : ((d : ZMod M) * x, (d : ZMod M) * y) = d • (x, y) := by
    ext <;> simp [zsmul_eq_mul]
  rw [hi, map_zsmul, zsmul_eq_mul]

/-- The finite test weight is literally the actual residue character after
coordinate reduction; no character correspondence is assumed. -/
theorem eisensteinFiniteWeight_cubicCoordinateWeight_reduction
    (A : ℤ) (hA : A ≠ 0) (M : ℕ) [NeZero M] (hdiv : 9 * A ∣ (M : ℤ))
    (r : Fin 2 → ZMod M) :
    eisensteinFiniteWeight
      (cubicThetaCoordinateWeight (cubicNumeratorHeckeCharacter A hA) M) r =
      (cubicNumeratorHeckeCharacter A hA).residue
        (cubicThetaResidueReduction A M hdiv
          (cubicThetaCoordinateHom M (r 0, r 1))) := by
  have hc : cubicThetaCoordinateHom M (r 0, r 1) =
      Ideal.Quotient.mk (cubicThetaRationalModulus M)
        (HeckeFamily.coordinateElement ((r 0).val : ℤ) ((r 1).val : ℤ)) := by
    simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using
      cubicThetaCoordinateHom_intCast M ((r 0).val : ℤ) ((r 1).val : ℤ)
  rw [hc, cubicThetaResidueReduction_mk]
  rfl

/-- Every actual cubic finite weight is invariant under an invertible
rational scalar, including residue classes where the weight vanishes. -/
theorem eisensteinFiniteWeight_cubicNumerator_int_mul
    (A : ℤ) (hA : A ≠ 0) (M : ℕ) [NeZero M] (hdiv : 9 * A ∣ (M : ℤ))
    (d : ℤ) (hd : IsUnit (d : EO ⧸ cubicNumeratorHeckeModulus A))
    (r : Fin 2 → ZMod M) :
    eisensteinFiniteWeight
      (cubicThetaCoordinateWeight (cubicNumeratorHeckeCharacter A hA) M)
      (fun i => (d : ZMod M) * r i) =
    eisensteinFiniteWeight
      (cubicThetaCoordinateWeight (cubicNumeratorHeckeCharacter A hA) M) r := by
  rw [eisensteinFiniteWeight_cubicCoordinateWeight_reduction A hA M hdiv,
    eisensteinFiniteWeight_cubicCoordinateWeight_reduction A hA M hdiv,
    cubicThetaCoordinateHom_int_mul, map_mul, map_intCast]
  exact cubicNumeratorHeckeCharacter_residue_int_mul A hA d hd _

/-- Determinant one supplies the required invertibility for the actual lower
right entry whenever the lower left entry is divisible by the conductor. -/
theorem eisensteinFiniteWeight_cubicNumerator_lowerRight
    (A : ℤ) (hA : A ≠ 0) (M : ℕ) [NeZero M] (hdiv : 9 * A ∣ (M : ℤ))
    (γ : SL(2, ℤ)) (hc : 9 * A ∣ γ 1 0) (r : Fin 2 → ZMod M) :
    eisensteinFiniteWeight
      (cubicThetaCoordinateWeight (cubicNumeratorHeckeCharacter A hA) M)
      (fun i => (γ 1 1 : ZMod M) * r i) =
    eisensteinFiniteWeight
      (cubicThetaCoordinateWeight (cubicNumeratorHeckeCharacter A hA) M) r :=
  eisensteinFiniteWeight_cubicNumerator_int_mul A hA M hdiv _
    (cubicTheta_lowerRight_isUnit A γ hc) r

/-- Every enlarged rational period realizes the same actual ideal theta as
an honest finite adelic test, with its exact factor six. -/
theorem theta_eisensteinFiniteTest_cubicNumerator_eq_six
    (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y ^ 3 = (A : OAI.CubicFirstMoment.Eisenstein))
    (M : ℕ) [NeZero M] (hdiv : 9 * A ∣ (M : ℤ)) (τ : ℍ) :
    theta (eisensteinFiniteTest
      (cubicThetaCoordinateWeight (cubicNumeratorHeckeCharacter A hA) M))
      (eisensteinSiegel τ) 0 =
      6 * heckeTheta (cubicNumeratorHeckeCharacter A hA) τ := by
  rw [theta_eisensteinFiniteTest]
  exact cubicThetaActual_weight_eq_six A hA hnoncube M hdiv τ

end ArtinMatthews
