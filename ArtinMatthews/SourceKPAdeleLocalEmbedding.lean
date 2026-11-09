module

public import ArtinMatthews.SourceKPAdeleLocalCover
public import ArtinMatthews.SourcePrimeExponents
public import Mathlib.GroupTheory.NoncommPiCoprod


set_option backward.privateInPublic true
@[expose] public section

/-! The local projective cubic covers embed in the actual adelic cover.
Their finite product has the shared cubic center inherited from the
global cover, and single-coordinate actions are exact. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups AdeleRing Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

theorem sourceKPAdeleLocalProjective_injective : Function.Injective (sourceKPAdeleLocalProjective K hζ P) := by
  apply (injective_iff_map_eq_one (sourceKPAdeleLocalProjective K hζ P)).mpr
  intro g hg
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (sourceFiniteKP2Scalar K hζ P).range g
  have hq : sourceKPAdeleLocalCover K hζ P x ∈ (sourceKPFiniteAdeleScalar K hζ).range :=
    (QuotientGroup.eq_one_iff _).mp hg
  obtain ⟨a, ha⟩ := hq
  have hb := congrArg SourceKPFiniteAdeleCover.base ha
  change GeneralLinearGroup.scalar (Fin 2) a = sourceKPAdeleSingleMatrix K P x.base at hb
  have hP := congrArg (sourceKPAdeleMatrixAt K P) hb
  rw [sourceKPAdeleMatrixAt_scalar, sourceKPAdeleSingleMatrix_same] at hP
  have hc := congrArg SourceKPFiniteAdeleCover.central ha
  change 1 = (sourceKPRootsTransport K hζ P).symm (x.central / sourceKPFinitePhase K hζ P x.base) at hc
  rw [← hP, sourceKPFinitePhase_scalar, div_one] at hc
  have hx : x.central = 1 := by
    apply (sourceKPRootsTransport K hζ P).symm.injective
    rw [map_one]
    exact hc.symm
  have hs : x = sourceFiniteKP2Scalar K hζ P (Units.map (sourceKPAdeleEval K P).toMonoidHom a) :=
    SourceFiniteKP2Cover.ext K hζ P hx hP.symm
  rw [hs]
  exact sourceFiniteKP2ProjectiveMk_scalar K hζ P _

theorem sourceKPAdelicLocalProjective_injective : Function.Injective (sourceKPAdelicLocalProjective K hζ P) :=
  fun _ _ h => sourceKPAdeleLocalProjective_injective K hζ P (congrArg Prod.snd h)

theorem sourceKPAdeleLocalProjective_center (z : rootsOfUnity 3 (P.adicCompletion K)) :
    sourceKPAdeleLocalProjective K hζ P (sourceFiniteKP2ProjectiveCenter K hζ P z) =
      sourceKPFiniteAdeleProjectiveCenter K hζ ((sourceKPRootsTransport K hζ P).symm z) := by
  change sourceKPFiniteAdeleProjectiveMk K hζ (sourceKPAdeleLocalCover K hζ P (sourceFiniteKP2Center K hζ P z)) =
    sourceKPFiniteAdeleProjectiveMk K hζ (sourceKPFiniteAdeleCenter K hζ ((sourceKPRootsTransport K hζ P).symm z))
  apply congrArg (sourceKPFiniteAdeleProjectiveMk K hζ)
  apply SourceKPFiniteAdeleCover.ext
  · change (sourceKPRootsTransport K hζ P).symm (z / sourceKPFinitePhase K hζ P 1) = _
    rw [sourceKPFinitePhase_one, div_one]
    rfl
  · exact (sourceKPAdeleSingleMatrix K P).map_one

theorem sourceKPAdelicLocalProjective_center (z : rootsOfUnity 3 (P.adicCompletion K)) :
    sourceKPAdelicLocalProjective K hζ P (sourceFiniteKP2ProjectiveCenter K hζ P z) =
      sourceKPAdelicProjectiveCenter K hζ ((sourceKPRootsTransport K hζ P).symm z) := by
  apply Prod.ext
  · rfl
  · exact sourceKPAdeleLocalProjective_center K hζ P z

variable (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (SourceExteriorPrime K S₀))

def sourceKPAdelicFiniteProduct :
    ((P : T) → SourceFiniteKP2Projective K hζ P.val.val) →* SourceKPAdelicProjective K hζ :=
  MonoidHom.noncommPiCoprod (fun P : T => sourceKPAdelicLocalProjective K hζ P.val.val) (by
    intro P Q hPQ g h
    exact sourceKPAdelicLocalProjective_commute K hζ P.val.val Q.val.val
      (fun he => hPQ (Subtype.ext (Subtype.ext he.symm))) g h)

theorem sourceKPAdelicFiniteProduct_single (P : T) (g : SourceFiniteKP2Projective K hζ P.val.val) :
    sourceKPAdelicFiniteProduct K hζ S₀ T (Pi.mulSingle P g) =
      sourceKPAdelicLocalProjective K hζ P.val.val g :=
  MonoidHom.noncommPiCoprod_mulSingle _ _ _

end
end ArtinMatthews
