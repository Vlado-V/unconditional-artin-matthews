module

public import ArtinMatthews.CubicThetaResiduePhaseCancellation
public import ArtinMatthews.CubicReciprocityNonprincipalConjugation
public import ArtinMatthews.CubicReciprocityNonprincipalCharacter


set_option backward.privateInPublic true
@[expose] public section

/-! Rational-twist cancellation for the actual cubic Fourier characters. -/

noncomputable section
namespace ArtinMatthews

open OAI OAI.SevenEighths
open scoped BigOperators

local notation "EO" => HeckeFamily.O

/-- Every noncube numerator gives zero rational-twist sum, at every
coordinate period divisible by its literal rational modulus. -/
theorem cubicThetaActual_rationalTwist_sum_eq_zero (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y ^ 3 = (A : OAI.CubicFirstMoment.Eisenstein))
    (M : ℕ) [NeZero M] (hdiv : 9 * A ∣ (M : ℤ)) (a : ℤ) :
    (∑ r : Fin M × Fin M,
      eisensteinRationalTwist
        (cubicThetaCoordinateWeight (cubicNumeratorHeckeCharacter A hA) M) a r) = 0 := by
  let χ := cubicNumeratorHeckeResidue A hA
  have hσ : ∀ u : (EO ⧸ cubicNumeratorHeckeModulus A)ˣ,
      χ (cubicNumeratorResidueConjugation A u) = (χ u)⁻¹ :=
    fun u => cubicNumeratorHeckeCharacter_residue_conjugate_inv A hA u
  have h3 : ∀ u : (EO ⧸ cubicNumeratorHeckeModulus A)ˣ, χ u ^ 3 = 1 := by
    intro u
    have h := congrArg (fun η : MulChar (EO ⧸ cubicNumeratorHeckeModulus A) ℂ => η u)
      (cubicNumeratorHeckeResidue_cube A hA)
    simpa only [MulChar.pow_apply_coe, MulChar.one_apply u.isUnit] using h
  exact cubicThetaResidue_phase_sum_eq_zero A M hdiv χ hσ h3
    (cubicNumeratorHeckeCharacter_nonprincipal A hA hnoncube) a

theorem cubicThetaActual_periodicCoeff (A : ℤ) (hA : A ≠ 0)
    (M : ℕ) [NeZero M] (hdiv : 9 * A ∣ (M : ℤ)) (n : ℤ × ℤ) :
    HeckeTheta.periodicCoeff
        (cubicThetaCoordinateWeight (cubicNumeratorHeckeCharacter A hA) M) n =
      HeckeFamily.elementCoeff (cubicNumeratorHeckeCharacter A hA)
        (HeckeFamily.coordinateElement n.1 n.2) := by
  apply cubicThetaCoordinateWeight_periodicCoeff
  exact cubicThetaRationalModulus_le A M hdiv (Ideal.subset_span (Set.mem_singleton _))

/-- The actual nonzero Fourier term supplies the noncube condition, so no
nonprincipality or cancellation hypothesis remains at this interface. -/
theorem cubicThetaFourier_rationalTwist_sum_eq_zero {S : Finset ℤ}
    (χ : AddChar (Additive (integerCubicGaloisGroup S)) ℂ) (hχ : χ ≠ 0)
    {A : ℤ} (hA : A ≠ 0) {R : integerCubicField S} (hR0 : R ≠ 0)
    (hR : R ^ 3 = (A : integerCubicField S))
    (hrep : ∀ σ : integerCubicGaloisGroup S,
      χ (Additive.ofMul σ) = ((σ.val R / R : integerCubicField S) : ℂ))
    (M : ℕ) [NeZero M] (hdiv : 9 * A ∣ (M : ℤ)) (a : ℤ) :
    (∑ r : Fin M × Fin M,
      eisensteinRationalTwist
        (cubicThetaCoordinateWeight (cubicNumeratorHeckeCharacter A hA) M) a r) = 0 :=
  cubicThetaActual_rationalTwist_sum_eq_zero A hA
    (cubicFourier_radical_not_cube_in_cubicMoment χ hχ hR0 hR hrep) M hdiv a

end ArtinMatthews
