module

public import ArtinMatthews.SourceArchOnlyIdele


set_option backward.privateInPublic true
@[expose] public section

/-! The actual split archimedean Borel acts by the normalized norm
character on every vector of the global inducing space. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField AdeleRing MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceArchOnlyTorus (a : (InfiniteAdeleRing K)ˣ) : sourceKPAdelicCubeTorus K hζ :=
  sourceKPAdelicCubeTorusEquiv K hζ (1, sourceArchOnlyCubeIdele K hζ a)

theorem sourceArchOnlyTorus_val (a : (InfiniteAdeleRing K)ˣ) :
    (sourceArchOnlyTorus K hζ a).val =
      (sourceKPProjectiveDiagonalHom (InfiniteAdeleRing K) a, 1) := by
  rw [sourceArchOnlyTorus, sourceKPAdelicCubeTorusEquiv_val]
  change sourceKPAdelicProjectiveCenter K hζ 1 *
    sourceKPAdelicProjectiveDiagonalLift K hζ (sourceArchOnlyIdele K a) = _
  rw [map_one, one_mul]
  apply Prod.ext
  · change sourceKPProjectiveDiagonalHom (InfiniteAdeleRing K)
      (sourceKPIdeleInfiniteUnit K (sourceArchOnlyIdele K a)) = _
    rw [sourceArchOnlyIdele_infinite]
  · change sourceKPFiniteAdeleProjectiveDiagonalLift K hζ
      (sourceKPIdeleFiniteUnit K (sourceArchOnlyIdele K a)) = 1
    rw [sourceArchOnlyIdele_finite, sourceKPFiniteAdeleProjectiveDiagonalLift_one]

theorem sourceArchOnlyTorus_idele (a : (InfiniteAdeleRing K)ˣ) :
    sourceKPAdelicTorusIdele K hζ
      (sourceKPAdelicTorusInducingCube K hζ (sourceArchOnlyTorus K hζ a)).val =
        sourceArchOnlyIdele K a := by
  apply sourceKPProjectiveDiagonalHom_injective 𝔸[K]
  rw [← sourceKPAdelicTorusIdele_projection]
  change sourceKPAdelicProjectiveProjection K hζ (sourceArchOnlyTorus K hζ a).val = _
  rw [sourceArchOnlyTorus, sourceKPAdelicCubeTorusEquiv_val,
    sourceKPAdelicCubeEmbedding_projection]
  rfl

theorem sourceArchOnlyTorus_character (s : ℂ) (a : (InfiniteAdeleRing K)ˣ) :
    sourceKPAdelicParametricCharacter K hζ s (sourceArchOnlyTorus K hζ a) =
      sourceKPIdeleComplexNorm K s (sourceArchOnlyIdele K a) := by
  rw [sourceArchOnlyTorus, sourceKPAdelicParametricCharacter_equiv, map_one, one_mul]
  rfl

def sourceArchOnlyBorel (x : InfiniteAdeleRing K) (a : (InfiniteAdeleRing K)ˣ) :
    sourceKPAdelicCoveringBorel K hζ :=
  sourceKPAdelicBorelCoordinatesEquiv K hζ
    ((x, 0), (sourceKPAdelicTorusInducingCube K hζ (sourceArchOnlyTorus K hζ a)).val)

theorem sourceArchOnlyBorel_val (x : InfiniteAdeleRing K) (a : (InfiniteAdeleRing K)ˣ) :
    (sourceArchOnlyBorel K hζ x a).val =
      (ProjGenLinGroup.mk (sourceKPUpperMatrix (InfiniteAdeleRing K) x) *
        sourceKPProjectiveDiagonalHom (InfiniteAdeleRing K) a, 1) := by
  change sourceKPAdelicUpperLift K hζ (x, 0) * (sourceArchOnlyTorus K hζ a).val = _
  rw [sourceArchOnlyTorus_val]
  apply Prod.ext
  · rfl
  · change sourceKPFiniteAdeleUpperLift K hζ 0 * 1 = 1
    rw [sourceKPFiniteAdeleUpperLift_zero, one_mul]

theorem sourceArchOnlyBorel_torus (x : InfiniteAdeleRing K) (a : (InfiniteAdeleRing K)ˣ) :
    sourceKPAdelicBorelTorusProjection K hζ (sourceArchOnlyBorel K hζ x a) =
      (sourceKPAdelicTorusInducingCube K hζ (sourceArchOnlyTorus K hζ a)).val :=
  sourceKPAdelicBorelTorusProjection_coordinates K hζ ((x,0) : 𝔸[K]) _

theorem sourceArchOnlyBorel_action (s : ℂ) (x : InfiniteAdeleRing K)
    (a : (InfiniteAdeleRing K)ˣ) (f : SourceKPAdelicTorusInducedSpace K hζ s) :
    sourceKPAdelicNormalizedBorelRepresentation K hζ s (sourceArchOnlyBorel K hζ x a) f =
      (sourceKPIdeleComplexNorm K (s+1/2) (sourceArchOnlyIdele K a) : ℂ) • f := by
  change sourceKPAdelicBorelModularHalf K hζ (sourceArchOnlyBorel K hζ x a) •
    sourceKPAdelicTorusInducedRepresentation K hζ s
      (sourceKPAdelicBorelTorusProjection K hζ (sourceArchOnlyBorel K hζ x a)) f = _
  have hh : sourceKPAdelicBorelModularHalf K hζ (sourceArchOnlyBorel K hζ x a) =
      (sourceKPIdeleComplexNorm K (1/2 : ℂ) (sourceArchOnlyIdele K a) : ℂ) := by
    change (sourceKPIdeleComplexNorm K (1/2 : ℂ) (sourceKPAdelicTorusIdele K hζ
      (sourceKPAdelicBorelTorusProjection K hζ (sourceArchOnlyBorel K hζ x a))) : ℂ) = _
    rw [sourceArchOnlyBorel_torus, sourceArchOnlyTorus_idele]
  rw [hh, sourceArchOnlyBorel_torus, sourceKPAdelicTorusInducedRepresentation_cube,
    sourceArchOnlyTorus_character, smul_smul, sourceKPIdeleComplexNorm_add, Units.val_mul, mul_comm]

theorem sourceArchOnlyBorel_covariant (s : ℂ) (x : InfiniteAdeleRing K)
    (a : (InfiniteAdeleRing K)ˣ) (f : SourceKPAdelicPrincipalSeries K hζ s)
    (g : SourceKPAdelicProjective K hζ) :
    f.val ((sourceArchOnlyBorel K hζ x a).val*g) =
      (sourceKPIdeleComplexNorm K (s+1/2) (sourceArchOnlyIdele K a) : ℂ) • f.val g := by
  rw [sourceAlgebraicInducedSpace_covariant, sourceArchOnlyBorel_action]

end
end ArtinMatthews
