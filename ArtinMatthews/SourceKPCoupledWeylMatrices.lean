module

public import ArtinMatthews.SourceKPCoupledLocalProduct
public import ArtinMatthews.SourceKPWeylLower


set_option backward.privateInPublic true
@[expose] public section

/-! Matrices whose finite components are identity or the actual Weyl
matrix admit the phase-one lift. This records the exact phase of the
finite Weyl test rather than only its projective matrix. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField AdeleRing MatrixGroups BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPCoupledWeyl_matrix_square {L : Type*} [Field L] :
    (sourceGL2Weyl : GL (Fin 2) L) * sourceGL2Weyl = 1 := by
  rw [← sourceKPWeylMatrix_field L, sourceKPWeylMatrix_square]

theorem sourceKPCoupledWeyl_twisted_multiplier (P : HeightOneSpectrum (𝓞 K)) :
    sourceKPFiniteTwistedMultiplier K hζ P sourceGL2Weyl sourceGL2Weyl = 1 := by
  let w : GL (Fin 2) (P.adicCompletion K) := sourceGL2Weyl
  have h : sourceFiniteKP2Multiplier K hζ P w w = 1 := by
    change sourceKP2Multiplier (sourceFiniteKPHilbert K hζ P) w sourceGL2Weyl = 1
    rw [sourceKP2Multiplier_right_weyl_formula _ (sourceFiniteKPHilbert_minus_right K hζ P),
      show w * sourceGL2Weyl = 1 from sourceKPCoupledWeyl_matrix_square,
      sourceKubotaX_one, show sourceKubotaX w = 1 from sourceKubotaX_weyl,
      div_one, map_one, MonoidHom.one_apply]
  change sourceKPFiniteTwistedMultiplier K hζ P w w = 1
  unfold sourceKPFiniteTwistedMultiplier sourceKPCochainTwist
  rw [show w * w = 1 from sourceKPCoupledWeyl_matrix_square,
    sourceKPFinitePhase_one, show sourceKPFinitePhase K hζ P w = 1 from sourceKPFinitePhase_weyl K hζ P,
    h, one_mul, one_mul, div_one]

def sourceKPCoupledWeylMatrices : Submonoid (GL (Fin 2) 𝔸ᶠ[K]) where
  carrier := {m | ∀ P : HeightOneSpectrum (𝓞 K),
    sourceKPAdeleMatrixAt K P m = 1 ∨ sourceKPAdeleMatrixAt K P m = sourceGL2Weyl}
  one_mem' := fun P => Or.inl (map_one (sourceKPAdeleMatrixAt K P))
  mul_mem' := by
    intro a b ha hb P
    change sourceKPAdeleMatrixAt K P (a*b) = 1 ∨ sourceKPAdeleMatrixAt K P (a*b) = sourceGL2Weyl
    rw [map_mul]
    rcases ha P with h₁ | h₁ <;> rcases hb P with h₂ | h₂ <;>
      rw [h₁,h₂]
    · exact Or.inl (one_mul 1)
    · exact Or.inr (one_mul _)
    · exact Or.inr (mul_one _)
    · exact Or.inl sourceKPCoupledWeyl_matrix_square

theorem sourceKPCoupledWeylMatrices_multiplier (a b : sourceKPCoupledWeylMatrices K) :
    sourceKPAdeleMultiplier K hζ a.val b.val = 1 := by
  unfold sourceKPAdeleMultiplier
  apply finprod_eq_one_of_forall_eq_one
  intro P
  rw [sourceKPAdeleLocalMultiplier]
  rcases a.property P with ha | ha <;> rcases b.property P with hb | hb <;> rw [ha,hb]
  · rw [sourceKPFiniteTwistedMultiplier_one_left, map_one]
  · rw [sourceKPFiniteTwistedMultiplier_one_left, map_one]
  · rw [sourceKPFiniteTwistedMultiplier_one_right, map_one]
  · rw [sourceKPCoupledWeyl_twisted_multiplier K hζ P, map_one]

def sourceKPCoupledWeylMatrixLift : sourceKPCoupledWeylMatrices K →* SourceKPFiniteAdeleProjective K hζ where
  toFun m := sourceKPFiniteAdeleProjectiveLift K hζ m.val
  map_one' := (sourceKPFiniteAdeleProjectiveMk K hζ).map_one
  map_mul' a b := (sourceKPFiniteAdeleProjectiveLift_mul_of_phase_one K hζ a.val b.val
    (sourceKPCoupledWeylMatrices_multiplier K hζ a b)).symm

def sourceKPCoupledFullWeylMatrix : sourceKPCoupledWeylMatrices K :=
  ⟨sourceKPWeylMatrix 𝔸ᶠ[K], fun P => Or.inr (sourceKPAdeleMatrixAt_weyl K P)⟩

def sourceKPCoupledSingleWeylMatrix (P : HeightOneSpectrum (𝓞 K)) : sourceKPCoupledWeylMatrices K :=
  ⟨sourceKPAdeleSingleMatrix K P sourceGL2Weyl, by
    intro Q
    by_cases h : Q = P
    · subst Q
      exact Or.inr (sourceKPAdeleSingleMatrix_same K P _)
    · exact Or.inl (sourceKPAdeleSingleMatrix_other K P Q h _)⟩

theorem sourceKPCoupledSingleWeylMatrix_lift (P : HeightOneSpectrum (𝓞 K)) :
    sourceKPCoupledWeylMatrixLift K hζ (sourceKPCoupledSingleWeylMatrix K P) =
      (sourceKPAdelicLocalProjective K hζ P
        (sourceFiniteKP2ProjectiveLift K hζ P sourceGL2Weyl)).2 := by
  change sourceKPFiniteAdeleProjectiveMk K hζ ⟨1, sourceKPAdeleSingleMatrix K P sourceGL2Weyl⟩ =
    sourceKPFiniteAdeleProjectiveMk K hζ
      (sourceKPAdeleLocalCover K hζ P (sourceFiniteKP2Lift K hζ P sourceGL2Weyl))
  apply congrArg (sourceKPFiniteAdeleProjectiveMk K hζ)
  apply SourceKPFiniteAdeleCover.ext
  · change 1 = (sourceKPRootsTransport K hζ P).symm (1 / sourceKPFinitePhase K hζ P sourceGL2Weyl)
    rw [sourceKPFinitePhase_weyl, div_one, map_one]
  · rfl

end
end ArtinMatthews
