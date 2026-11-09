module

public import ArtinMatthews.SourceArchCubeAction
public import ArtinMatthews.SourceArchOnlyCompact
public import ArtinMatthews.SourceArchProductNorm


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open SourceArchJacquet
open scoped NumberField AdeleRing MatrixGroups BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceArchNormalizedBorel_covariant (s : ℂ)
    (b : GL (Fin 2) (InfiniteAdeleRing K))
    (hb : b ∈ sourceKPRingNormalizedBorel (InfiniteAdeleRing K))
    (f : SourceKPAdelicPrincipalSeries K hζ s) (q : SourceKPAdelicProjective K hζ) :
    f.val ((ProjGenLinGroup.mk b,1)*q) =
      (sourceKPIdeleComplexNorm K (s+1/2)
        (sourceArchOnlyIdele K (GeneralLinearGroup.det b)) : ℂ) • f.val q := by
  have he : (sourceArchOnlyBorel K hζ (b 0 1) (GeneralLinearGroup.det b)).val =
      (ProjGenLinGroup.mk b,1) := by
    rw [sourceArchOnlyBorel_val]
    apply Prod.ext
    · change ProjGenLinGroup.mk (sourceKPUpperMatrix (InfiniteAdeleRing K) (b 0 1)) *
        sourceKPProjectiveDiagonalHom (InfiniteAdeleRing K) (GeneralLinearGroup.det b) =
          ProjGenLinGroup.mk b
      change ProjGenLinGroup.mk (sourceKPUpperMatrix (InfiniteAdeleRing K) (b 0 1)) *
        ProjGenLinGroup.mk (sourceKPDiagonalHom (InfiniteAdeleRing K) (GeneralLinearGroup.det b)) =
          ProjGenLinGroup.mk b
      simpa only [map_mul] using congrArg
        (fun m : GL (Fin 2) (InfiniteAdeleRing K) => ProjGenLinGroup.mk m)
        (sourceKPRingNormalizedBorel_factor (InfiniteAdeleRing K) b hb).symm
    · rfl
  rw [← he, sourceArchOnlyBorel_covariant]

theorem sourceArchNormalizedBorel_scalar (s : ℂ)
    (b : GL (Fin 2) (InfiniteAdeleRing K))
    (hb : b ∈ sourceKPRingNormalizedBorel (InfiniteAdeleRing K))
    (q : SourceKPAdelicProjective K hζ) :
    sourceKPAdelicCompactScalar K hζ s ((ProjGenLinGroup.mk b,1)*q) =
      (sourceKPIdeleComplexNorm K (s+1/2)
        (sourceArchOnlyIdele K (GeneralLinearGroup.det b)) : ℂ) *
        sourceKPAdelicCompactScalar K hζ s q := by
  unfold sourceKPAdelicCompactScalar
  rw [sourceArchNormalizedBorel_covariant K hζ s b hb]
  rfl

theorem sourceArchCompactScalar_factor_matrix (s : ℂ)
    (g : GL (Fin 2) (InfiniteAdeleRing K)) (qf : SourceKPFiniteAdeleProjective K hζ) :
    sourceKPAdelicCompactScalar K hζ s (ProjGenLinGroup.mk g,qf) =
      (∏ v : InfinitePlace K,
        sourceArchSphericalGL s (sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v))) *
      sourceKPAdelicCompactScalar K hζ s (1,qf) := by
  let b := sourceKPArchIwasawaBorel K hζ g
  let k := sourceKPArchIwasawaCompact K hζ g
  have he : (ProjGenLinGroup.mk g,qf) =
      (((ProjGenLinGroup.mk b,1) * (1,qf)) * (ProjGenLinGroup.mk k,1) :
        SourceKPAdelicProjective K hζ) := by
    apply Prod.ext
    · change ProjGenLinGroup.mk g = (ProjGenLinGroup.mk b * 1) * ProjGenLinGroup.mk k
      rw [mul_one, sourceKPArchIwasawa_factor K hζ g, map_mul, map_mul,
        ProjGenLinGroup.mk_scalar, mul_one]
    · simp
  rw [he, sourceArchCompactScalar_right K hζ s _ k (sourceArchIwasawaCompact_mem K hζ g),
    sourceArchNormalizedBorel_scalar K hζ s b (sourceKPArchIwasawaBorel_mem K hζ g),
    sourceArchIwasawa_character_product]

def sourceArchProjectiveAt (v : InfinitePlace K) : PGL(2, InfiniteAdeleRing K) →* PGL(2, ℂ) :=
  ProjGenLinGroup.map ((sourceKPArchComplexEquiv K hζ v).toRingHom.comp (sourceArchAdeleEval K v))

def sourceArchSphericalProduct (s : ℂ) (g : PGL(2, InfiniteAdeleRing K)) : ℂ :=
  ∏ v : InfinitePlace K, sourceArchSphericalSection s (sourceArchProjectiveAt K hζ v g)

theorem sourceArchProjectiveAt_mk (v : InfinitePlace K) (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    sourceArchProjectiveAt K hζ v (ProjGenLinGroup.mk g) =
      ProjGenLinGroup.mk (sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v)) := by
  rw [sourceArchProjectiveAt, ProjGenLinGroup.map_mk]
  apply congrArg ProjGenLinGroup.mk
  apply GeneralLinearGroup.ext
  intro i j
  rfl

theorem sourceArchSphericalProduct_mk (s : ℂ) (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    sourceArchSphericalProduct K hζ s (ProjGenLinGroup.mk g) =
      ∏ v : InfinitePlace K,
        sourceArchSphericalGL s (sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v)) := by
  simp only [sourceArchSphericalProduct, sourceArchProjectiveAt_mk, sourceArchSphericalSection_mk]

theorem sourceArchCompactScalar_factor (s : ℂ) (g : PGL(2, InfiniteAdeleRing K))
    (qf : SourceKPFiniteAdeleProjective K hζ) :
    sourceKPAdelicCompactScalar K hζ s (g,qf) =
      sourceArchSphericalProduct K hζ s g * sourceKPAdelicCompactScalar K hζ s (1,qf) := by
  obtain ⟨g,rfl⟩ := ProjGenLinGroup.mk_surjective g
  rw [sourceArchSphericalProduct_mk, sourceArchCompactScalar_factor_matrix]

end
end ArtinMatthews
