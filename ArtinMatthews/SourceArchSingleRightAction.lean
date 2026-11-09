module

public import ArtinMatthews.SourceArchSectionFactorization


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open SourceArchJacquet
open scoped NumberField AdeleRing MatrixGroups BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceArchMatrixSingle (v : InfinitePlace K) (a : GL (Fin 2) ℂ) :
    GL (Fin 2) (InfiniteAdeleRing K) :=
  (sourceArchGLPiEquiv K).symm (fun w => (sourceKPArchMatrixComplexEquiv K hζ w).symm
    ((Pi.mulSingle v a : InfinitePlace K → GL (Fin 2) ℂ) w))

theorem sourceArchMatrixSingle_at (v w : InfinitePlace K) (a : GL (Fin 2) ℂ) :
    sourceKPArchMatrixComplexEquiv K hζ w
      (sourceArchGLPiEquiv K (sourceArchMatrixSingle K hζ v a) w) =
        (Pi.mulSingle v a : InfinitePlace K → GL (Fin 2) ℂ) w := by
  simp only [sourceArchMatrixSingle, MulEquiv.apply_symm_apply]

theorem sourceArchMatrixSingle_one (v : InfinitePlace K) : sourceArchMatrixSingle K hζ v 1 = 1 := by
  apply (sourceArchGLPiEquiv K).injective
  funext w
  apply (sourceKPArchMatrixComplexEquiv K hζ w).injective
  rw [sourceArchMatrixSingle_at, map_one, Pi.one_apply, map_one]
  simp

def sourceArchGroupSingle (v : InfinitePlace K) (a : GL (Fin 2) ℂ) : SourceKPAdelicProjective K hζ :=
  (ProjGenLinGroup.mk (sourceArchMatrixSingle K hζ v a),1)

theorem sourceArchGroupSingle_one (v : InfinitePlace K) : sourceArchGroupSingle K hζ v 1 = 1 := by
  rw [sourceArchGroupSingle, sourceArchMatrixSingle_one, map_one]
  rfl

def sourceArchOtherScalar (s : ℂ) (g : GL (Fin 2) (InfiniteAdeleRing K))
    (qf : SourceKPFiniteAdeleProjective K hζ) (v : InfinitePlace K) : ℂ :=
  (∏ w ∈ (Finset.univ.erase v), sourceArchSphericalGL s
    (sourceKPArchMatrixComplexEquiv K hζ w (sourceArchGLPiEquiv K g w))) *
      sourceKPAdelicCompactScalar K hζ s (1,qf)

theorem sourceArchCompactScalar_single_right (s : ℂ)
    (g : GL (Fin 2) (InfiniteAdeleRing K)) (qf : SourceKPFiniteAdeleProjective K hζ)
    (v : InfinitePlace K) (a : GL (Fin 2) ℂ) :
    sourceKPAdelicCompactScalar K hζ s ((ProjGenLinGroup.mk g,qf)*sourceArchGroupSingle K hζ v a) =
      sourceArchSphericalGL s
        (sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v)*a) *
          sourceArchOtherScalar K hζ s g qf v := by
  classical
  change sourceKPAdelicCompactScalar K hζ s
    (ProjGenLinGroup.mk g * ProjGenLinGroup.mk (sourceArchMatrixSingle K hζ v a),qf*1) = _
  rw [mul_one, ← map_mul, sourceArchCompactScalar_factor_matrix]
  simp only [map_mul, Pi.mul_apply, sourceArchMatrixSingle_at]
  have hprod : (∏ w : InfinitePlace K, sourceArchSphericalGL s
      (sourceKPArchMatrixComplexEquiv K hζ w (sourceArchGLPiEquiv K g w)*
        (Pi.mulSingle v a : InfinitePlace K → GL (Fin 2) ℂ) w)) =
      sourceArchSphericalGL s (sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v)*a) *
        ∏ w ∈ (Finset.univ.erase v), sourceArchSphericalGL s
          (sourceKPArchMatrixComplexEquiv K hζ w (sourceArchGLPiEquiv K g w)) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v), Pi.mulSingle_eq_same]
    congr 1
    apply Finset.prod_congr rfl
    intro w hw
    rw [Pi.mulSingle_eq_of_ne (Finset.mem_erase.mp hw).1, mul_one]
  rw [hprod, sourceArchOtherScalar]
  ring

theorem sourceArchCompactScalar_single_base (s : ℂ)
    (g : GL (Fin 2) (InfiniteAdeleRing K)) (qf : SourceKPFiniteAdeleProjective K hζ)
    (v : InfinitePlace K) :
    sourceKPAdelicCompactScalar K hζ s (ProjGenLinGroup.mk g,qf) =
      sourceArchSphericalGL s (sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v)) *
        sourceArchOtherScalar K hζ s g qf v := by
  simpa only [sourceArchGroupSingle_one, mul_one] using
    sourceArchCompactScalar_single_right K hζ s g qf v 1

end
end ArtinMatthews
