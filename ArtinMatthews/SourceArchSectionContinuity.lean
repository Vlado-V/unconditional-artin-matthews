module

public import ArtinMatthews.SourceArchSectionFactorization
public import ArtinMatthews.SourceArchSphericalContinuity


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open SourceArchJacquet
open scoped NumberField AdeleRing MatrixGroups BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceArchComplexEquiv_continuous (v : InfinitePlace K) :
    Continuous (sourceKPArchComplexEquiv K hζ v) := by
  apply Isometry.continuous
  apply isometry_iff_dist_eq.mpr
  intro x y
  rw [dist_eq_norm, dist_eq_norm, ← map_sub, sourceKPArchComplexEquiv_norm]

theorem sourceArchMatrixAt_continuous (v : InfinitePlace K) :
    Continuous (fun g : GL (Fin 2) (InfiniteAdeleRing K) =>
      sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v)) := by
  let f : InfiniteAdeleRing K →+* ℂ :=
    (sourceKPArchComplexEquiv K hζ v).toRingHom.comp (sourceArchAdeleEval K v)
  have hf : Continuous f := (sourceArchComplexEquiv_continuous K hζ v).comp
    (_root_.continuous_apply v)
  have he : (fun g : GL (Fin 2) (InfiniteAdeleRing K) =>
      sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v)) =
        GeneralLinearGroup.map (n := Fin 2) f := by
    funext g
    apply GeneralLinearGroup.ext
    intro i j
    rfl
  rw [he]
  exact hf.generalLinearGroup_map (n := Fin 2)

theorem sourceArchSphericalProduct_matrix_continuous (s : ℂ) :
    Continuous (fun g : GL (Fin 2) (InfiniteAdeleRing K) =>
      sourceArchSphericalProduct K hζ s (ProjGenLinGroup.mk g)) := by
  simp_rw [sourceArchSphericalProduct_mk]
  apply continuous_finsetProd
  intro v _
  exact (sourceArchSphericalGL_continuous s).comp (sourceArchMatrixAt_continuous K hζ v)

theorem sourceArchCompactScalar_continuous (s : ℂ) (qf : SourceKPFiniteAdeleProjective K hζ) :
    Continuous (fun g : GL (Fin 2) (InfiniteAdeleRing K) =>
      sourceKPAdelicCompactScalar K hζ s (ProjGenLinGroup.mk g,qf)) := by
  have he : (fun g : GL (Fin 2) (InfiniteAdeleRing K) =>
      sourceKPAdelicCompactScalar K hζ s (ProjGenLinGroup.mk g,qf)) =
      fun g => sourceArchSphericalProduct K hζ s (ProjGenLinGroup.mk g) *
        sourceKPAdelicCompactScalar K hζ s (1,qf) := by
    funext g
    exact sourceArchCompactScalar_factor K hζ s (ProjGenLinGroup.mk g) qf
  rw [he]
  exact (sourceArchSphericalProduct_matrix_continuous K hζ s).mul continuous_const

end
end ArtinMatthews
