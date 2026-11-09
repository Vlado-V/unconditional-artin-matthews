module

public import ArtinMatthews.SourceKPFiniteAdeleProjective
public import ArtinMatthews.SourceKPRationalLiftPhase


set_option backward.privateInPublic true
@[expose] public section

/-! The actual rational splitting of the finite adelic cubic cover.
Its phase is the inverse cochain product, and the splitting descends
through the ordinary scalar quotient to the actual projective group. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups AdeleRing BigOperators
noncomputable section
variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPFiniteAdeleRationalLift : GL (Fin 2) K →* SourceKPFiniteAdeleCover K hζ where
  toFun g := ⟨sourceKPRationalLiftPhase K hζ g, sourceKPRationalDiagonal K g⟩
  map_one' := by
    apply SourceKPFiniteAdeleCover.ext
    · exact sourceKPRationalLiftPhase_one K hζ
    · exact map_one _
  map_mul' g h := by
    apply SourceKPFiniteAdeleCover.ext
    · exact sourceKPRationalLiftPhase_mul K hζ g h
    · exact map_mul _ _ _

theorem sourceKPFiniteAdeleRationalLift_phase (g : GL (Fin 2) K) :
    (sourceKPFiniteAdeleRationalLift K hζ g).central =
      (∏ᶠ P, sourceKPRationalLocalPhase K hζ g P)⁻¹ := rfl

theorem sourceKPFiniteAdeleRationalLift_projection (g : GL (Fin 2) K) :
    sourceKPFiniteAdeleProjection K hζ (sourceKPFiniteAdeleRationalLift K hζ g) =
      sourceKPRationalDiagonal K g := rfl

theorem sourceKPFiniteAdeleRationalLift_scalar (u : Kˣ) :
    sourceKPFiniteAdeleRationalLift K hζ (GeneralLinearGroup.scalar (Fin 2) u) =
      sourceKPFiniteAdeleScalar K hζ (FiniteAdeleRing.unitEmbedding (𝓞 K) K u) := by
  apply SourceKPFiniteAdeleCover.ext
  · exact sourceKPRationalLiftPhase_scalar K hζ u
  · exact GeneralLinearGroup.map_scalar (algebraMap K 𝔸ᶠ[K]) u

def sourceKPFiniteAdeleProjectiveRationalLift :
    PGL(2, K) →* SourceKPFiniteAdeleProjective K hζ :=
  QuotientGroup.lift _ ((sourceKPFiniteAdeleProjectiveMk K hζ).comp (sourceKPFiniteAdeleRationalLift K hζ)) (by
    intro g hg
    rw [GeneralLinearGroup.center_eq_range_scalar] at hg
    obtain ⟨u, rfl⟩ := hg
    change sourceKPFiniteAdeleProjectiveMk K hζ
      (sourceKPFiniteAdeleRationalLift K hζ (GeneralLinearGroup.scalar (Fin 2) u)) = 1
    rw [sourceKPFiniteAdeleRationalLift_scalar, sourceKPFiniteAdeleProjectiveMk_scalar])

theorem sourceKPFiniteAdeleProjectiveRationalLift_mk (g : GL (Fin 2) K) :
    sourceKPFiniteAdeleProjectiveRationalLift K hζ (ProjGenLinGroup.mk g) =
      sourceKPFiniteAdeleProjectiveMk K hζ
        ⟨(∏ᶠ P, sourceKPRationalLocalPhase K hζ g P)⁻¹, sourceKPRationalDiagonal K g⟩ := rfl

theorem sourceKPFiniteAdeleProjectiveRationalLift_projection (g : PGL(2, K)) :
    sourceKPFiniteAdeleProjectiveProjection K hζ (sourceKPFiniteAdeleProjectiveRationalLift K hζ g) =
      ProjGenLinGroup.map (algebraMap K 𝔸ᶠ[K]) g := by
  induction g using ProjGenLinGroup.induction_on with
  | mk g => rfl

end
end ArtinMatthews
