module

public import ArtinMatthews.SourceArchSectionContinuity
public import ArtinMatthews.SourceKPAdelicConstantTermPeriodization


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open SourceArchJacquet
open scoped NumberField AdeleRing MatrixGroups
noncomputable section

theorem sourceKPUpperMatrix_continuous (R : Type*) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] : Continuous (sourceKPUpperMatrix R) := by
  have he : sourceKPUpperMatrix R = GeneralLinearGroup.upperRightHom := by
    funext x
    apply GeneralLinearGroup.ext
    intro i j
    rfl
  rw [he]
  exact GeneralLinearGroup.continuous_upperRightHom

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceArchSphericalProduct_openCell_continuous (s : ℂ)
    (g : PGL(2, InfiniteAdeleRing K)) :
    Continuous (fun x : InfiniteAdeleRing K => sourceArchSphericalProduct K hζ s
      (ProjGenLinGroup.mk (sourceKPWeylMatrix (InfiniteAdeleRing K)) *
        ProjGenLinGroup.mk (sourceKPUpperMatrix (InfiniteAdeleRing K) x) * g)) := by
  obtain ⟨g,rfl⟩ := ProjGenLinGroup.mk_surjective g
  simp_rw [← map_mul]
  exact (sourceArchSphericalProduct_matrix_continuous K hζ s).comp
    ((continuous_const.mul (sourceKPUpperMatrix_continuous (InfiniteAdeleRing K))).mul continuous_const)

theorem sourceArchOpenCell_continuous (s : ℂ)
    (g : GL (Fin 2) (InfiniteAdeleRing K)) (qf : SourceKPFiniteAdeleProjective K hζ) :
    Continuous (fun x : InfiniteAdeleRing K => sourceKPAdelicCompactScalar K hζ s
      (ProjGenLinGroup.mk (sourceKPWeylMatrix (InfiniteAdeleRing K) *
        sourceKPUpperMatrix (InfiniteAdeleRing K) x * g),qf)) :=
  (sourceArchCompactScalar_continuous K hζ s qf).comp
    ((continuous_const.mul (sourceKPUpperMatrix_continuous (InfiniteAdeleRing K))).mul continuous_const)

theorem sourceKPAdelicIntertwiningKernel_arch_continuous (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (yf : 𝔸ᶠ[K]) :
    Continuous (fun x : InfiniteAdeleRing K => sourceKPAdelicIntertwiningKernel K hζ s g (x,yf)) := by
  obtain ⟨gI,hgI⟩ := ProjGenLinGroup.mk_surjective g.1
  let qf := (sourceKPAdelicProjectiveWeyl K hζ).2 * sourceKPFiniteAdeleUpperLift K hζ yf * g.2
  have hw : (sourceKPAdelicProjectiveWeyl K hζ).1 =
      ProjGenLinGroup.mk (sourceKPWeylMatrix (InfiniteAdeleRing K)) := by
    change ProjGenLinGroup.map (algebraMap K (InfiniteAdeleRing K))
      (ProjGenLinGroup.mk (sourceKPWeylMatrix K)) = _
    rw [ProjGenLinGroup.map_mk, sourceKPWeylMatrix_map]
  have he (x : InfiniteAdeleRing K) :
      sourceKPAdelicProjectiveWeyl K hζ * sourceKPAdelicUpperLift K hζ (x,yf) * g =
        (ProjGenLinGroup.mk (sourceKPWeylMatrix (InfiniteAdeleRing K) *
          sourceKPUpperMatrix (InfiniteAdeleRing K) x * gI),qf) := by
    apply Prod.ext
    · simp only [Prod.fst_mul, hw]
      change (ProjGenLinGroup.mk (sourceKPWeylMatrix (InfiniteAdeleRing K)) *
        ProjGenLinGroup.mk (sourceKPUpperMatrix (InfiniteAdeleRing K) x)) * g.1 = _
      rw [← hgI, map_mul, map_mul]
    · rfl
  simp_rw [sourceKPAdelicIntertwiningKernel, he]
  exact sourceArchOpenCell_continuous K hζ s gI qf

end
end ArtinMatthews
