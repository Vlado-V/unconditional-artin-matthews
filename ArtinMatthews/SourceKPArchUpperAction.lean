module

public import ArtinMatthews.SourceArchProjectiveGramAction
public import ArtinMatthews.SourceKPArchGramQuotient


set_option backward.privateInPublic true
@[expose] public section

/-! The literal product upper-half-space action and the actual symmetric-coordinate equivariance. -/
namespace ArtinMatthews
open NumberField Matrix Matrix.GeneralLinearGroup SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPArchProjectiveAt (hζ : IsPrimitiveRoot ζ 12) (v : InfinitePlace K) :
    PGL(2, InfiniteAdeleRing K) →* PGL(2, ℂ) :=
  ProjGenLinGroup.map ((sourceKPArchComplexEquiv K hζ v).toRingHom.comp (sourceArchAdeleEval K v))

lemma sourceKPArchProjectiveAt_mk (v : InfinitePlace K) (a : GL (Fin 2) (InfiniteAdeleRing K)) :
    sourceKPArchProjectiveAt K hζ v (ProjGenLinGroup.mk a) =
      ProjGenLinGroup.mk (sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K a v)) := by
  rw [sourceKPArchProjectiveAt, ProjGenLinGroup.map_mk]
  congr 1

def sourceKPArchUpperAction (hζ : IsPrimitiveRoot ζ 12) (a : PGL(2, InfiniteAdeleRing K))
    (p : SourceKPArchUpperHalfSpace K) : SourceKPArchUpperHalfSpace K :=
  fun v => sourceArchProjectiveUpperAction (sourceKPArchProjectiveAt K hζ v a) (p v)

lemma sourceKPArchUpperAction_one (p : SourceKPArchUpperHalfSpace K) :
    sourceKPArchUpperAction K hζ 1 p = p := by
  funext v
  change sourceArchProjectiveUpperAction (sourceKPArchProjectiveAt K hζ v 1) (p v) = p v
  rw [map_one, sourceArchProjectiveUpperAction_one]

lemma sourceKPArchUpperAction_mul (a b : PGL(2, InfiniteAdeleRing K))
    (p : SourceKPArchUpperHalfSpace K) :
    sourceKPArchUpperAction K hζ (a * b) p =
      sourceKPArchUpperAction K hζ a (sourceKPArchUpperAction K hζ b p) := by
  funext v
  change sourceArchProjectiveUpperAction (sourceKPArchProjectiveAt K hζ v (a * b)) (p v) =
    sourceArchProjectiveUpperAction (sourceKPArchProjectiveAt K hζ v a)
      (sourceArchProjectiveUpperAction (sourceKPArchProjectiveAt K hζ v b) (p v))
  rw [map_mul, sourceArchProjectiveUpperAction_mul]

@[instance_reducible]
def sourceKPArchUpperMulAction (hζ : IsPrimitiveRoot ζ 12) :
    MulAction (PGL(2, InfiniteAdeleRing K)) (SourceKPArchUpperHalfSpace K) where
  smul := sourceKPArchUpperAction K hζ
  one_smul := sourceKPArchUpperAction_one K hζ
  mul_smul := sourceKPArchUpperAction_mul K hζ

lemma sourceKPArchUpperAction_continuous (a : PGL(2, InfiniteAdeleRing K)) :
    Continuous (sourceKPArchUpperAction K hζ a) := by
  apply continuous_pi
  intro v
  exact (sourceArchProjectiveUpperAction_continuous _).comp (continuous_apply v)

lemma sourceKPArchGramCoordinatesMatrix_mul (a b : GL (Fin 2) (InfiniteAdeleRing K)) :
    sourceKPArchGramCoordinatesMatrix K hζ (a * b) =
      sourceKPArchUpperAction K hζ (ProjGenLinGroup.mk a) (sourceKPArchGramCoordinatesMatrix K hζ b) := by
  funext v
  rw [sourceKPArchUpperAction, sourceKPArchProjectiveAt_mk, sourceArchProjectiveUpperAction_mk]
  change sourceArchGramCoordinates
    (sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K (a * b) v)) = _
  rw [map_mul, Pi.mul_apply, map_mul]
  exact sourceArchGramCoordinates_mul _ _

lemma sourceKPArchSymmetricHomeomorph_smul (a : PGL(2, InfiniteAdeleRing K))
    (p : SourceKPArchSymmetricSpace K hζ) :
    sourceKPArchSymmetricHomeomorph K hζ (a • p) =
      sourceKPArchUpperAction K hζ a (sourceKPArchSymmetricHomeomorph K hζ p) := by
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective p
  obtain ⟨a, rfl⟩ := ProjGenLinGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := ProjGenLinGroup.mk_surjective b
  exact sourceKPArchGramCoordinatesMatrix_mul K hζ a b

lemma sourceKPArchSymmetric_action_continuous (a : PGL(2, InfiniteAdeleRing K)) :
    Continuous (fun p : SourceKPArchSymmetricSpace K hζ => a • p) := by
  have he : (fun p : SourceKPArchSymmetricSpace K hζ => a • p) =
      (sourceKPArchSymmetricHomeomorph K hζ).symm ∘ sourceKPArchUpperAction K hζ a ∘
        sourceKPArchSymmetricHomeomorph K hζ := by
    funext p
    apply (sourceKPArchSymmetricHomeomorph K hζ).injective
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply, sourceKPArchSymmetricHomeomorph_smul]
  rw [he]
  exact (sourceKPArchSymmetricHomeomorph K hζ).symm.continuous.comp
    ((sourceKPArchUpperAction_continuous K hζ a).comp (sourceKPArchSymmetricHomeomorph K hζ).continuous)

end
end ArtinMatthews
