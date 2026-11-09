module

public import ArtinMatthews.CubicThetaScalarComparison
public import ArtinMatthews.CubicThetaUnweightedCongruence


set_option backward.privateInPublic true
@[expose] public section

/-! Exact integral-matrix specialization of the unweighted scalar comparison. -/
noncomputable section
namespace ArtinMatthews

open Complex UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups
open OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

@[simp] theorem cubicTheta_rationalMatrix_entry (γ : SL(2, ℤ)) (i j : Fin 2) :
    (γ : SL(2, ℚ)) i j = (γ i j : ℚ) := by
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ => M i j)
    (Matrix.SpecialLinearGroup.coe_matrix_coe (R := ℚ) γ)
  exact h

theorem cubicTheta_rationalMatrix_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    (γ : SL(2, ℚ)) • τ = γ • τ := by
  apply UpperHalfPlane.ext
  erw [UpperHalfPlane.coe_specialLinearGroup_apply]

/-- The proved unweighted Γ₀(3) multiplier also holds under the literal
rational matrix used by the symplectic embedding. -/
theorem eisensteinHolomorphicTheta_rational_Gamma0_three (γ : SL(2, ℤ))
    (hγ : γ ∈ Gamma0 3) (τ : ℍ) :
    eisensteinHolomorphicTheta ((γ : SL(2, ℚ)) • τ) =
      cubicThetaNebentypus (γ 1 1) *
        (((γ : SL(2, ℚ)) 1 0 : ℂ) * τ + ((γ : SL(2, ℚ)) 1 1 : ℂ)) *
          eisensteinHolomorphicTheta τ := by
  simpa only [cubicTheta_rationalMatrix_smul, cubicTheta_rationalMatrix_entry,
    Rat.cast_intCast] using eisensteinHolomorphicTheta_Gamma0_three γ hγ τ

variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

/-- The exact Γ₀ multiplier transfers to every test with the proved common
finite scalar. Arithmetic production of those scalar equations is separate. -/
theorem eisensteinTheta_integer_common_scalar_transform
    (D : WeilData (Fin 2) MpR MpF MpA) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 3)
    (M : ℕ) [NeZero M] (c : ℂ)
    (hbase : D.finiteAction (eisensteinSymplectic (γ : SL(2, ℚ)))
      (eisensteinFiniteTest (fun _ : Fin M × Fin M => (1 : ℂ))) =
        c • eisensteinFiniteTest (fun _ : Fin M × Fin M => (1 : ℂ)))
    (φ : finiteSchwartz (Fin 2))
    (hφ : D.finiteAction (eisensteinSymplectic (γ : SL(2, ℚ))) φ = c • φ) (τ : ℍ) :
    theta φ (eisensteinSiegel (γ • τ)) 0 =
      cubicThetaNebentypus (γ 1 1) * ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) *
        theta φ (eisensteinSiegel τ) 0 := by
  have h := eisensteinTheta_common_scalar_transform D (γ : SL(2, ℚ))
    (cubicThetaNebentypus (γ 1 1))
    (eisensteinHolomorphicTheta_rational_Gamma0_three γ hγ) M c hbase φ hφ τ
  simpa only [cubicTheta_rationalMatrix_smul, cubicTheta_rationalMatrix_entry,
    Rat.cast_intCast] using h

end ArtinMatthews
