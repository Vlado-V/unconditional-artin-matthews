module

public import ArtinMatthews.SourceKPAdelicProjectiveHeight
public import ArtinMatthews.SourceKPFiniteLevelTopology
public import ArtinMatthews.SourceKPHeightLocalContinuity


set_option backward.privateInPublic true
@[expose] public section

/-! Continuity of the actual height on each archimedean fiber. The finite
coordinate contributes a fixed scalar. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup Topology
open SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing BigOperators
noncomputable section

theorem sourceArchHeight_continuous : Continuous sourceArchHeight := by
  have he (i j : Fin 2) : Continuous (fun g : GL (Fin 2) ℂ => ‖g i j‖) :=
    (Units.continuous_val.matrix_elem i j).norm
  have hd : Continuous (fun g : GL (Fin 2) ℂ => ‖(GeneralLinearGroup.det g : ℂ)‖) :=
    (Units.continuous_val.comp GeneralLinearGroup.continuous_det).norm
  exact hd.div (((he 1 0).pow 2).add ((he 1 1).pow 2))
    (fun g => (sourceArchBottomNorm_pos g).ne')

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPArchMatrixHeight (a : GL (Fin 2) (InfiniteAdeleRing K)) : ℝ :=
  ∏ v : InfinitePlace K,
    sourceArchHeight (sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K a v)) ^ v.mult

def sourceKPFiniteMatrixHeightProduct (b : GL (Fin 2) 𝔸ᶠ[K]) : ℝ :=
  ∏ᶠ P : HeightOneSpectrum (𝓞 K), sourceKPFiniteMatrixHeight K P (sourceKPAdeleMatrixAt K P b)

theorem sourceKPArchMatrixHeightAt_continuous (v : InfinitePlace K) :
    Continuous (fun a : GL (Fin 2) (InfiniteAdeleRing K) =>
      sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K a v)) := by
  let φ : InfiniteAdeleRing K →+* ℂ := (sourceKPArchComplexEquiv K hζ v).toRingHom.comp
    (sourceArchAdeleEval K v)
  have hφ : Continuous φ :=
    (sourceKPArchComplexEquiv_continuous K hζ v).comp (continuous_apply v)
  have he (a : GL (Fin 2) (InfiniteAdeleRing K)) :
      GeneralLinearGroup.map φ a =
        sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K a v) := by
    apply GeneralLinearGroup.ext
    intro i j
    rfl
  exact hφ.generalLinearGroup_map.congr he

theorem sourceKPArchMatrixHeight_continuous : Continuous (sourceKPArchMatrixHeight K hζ) :=
  continuous_finsetProd Finset.univ (fun v _ =>
    (sourceArchHeight_continuous.comp (sourceKPArchMatrixHeightAt_continuous K hζ v)).pow v.mult)

theorem sourceKPAdelicHeight_pair (a : GL (Fin 2) (InfiniteAdeleRing K)) (b : GL (Fin 2) 𝔸ᶠ[K]) :
    sourceKPAdelicHeight K hζ ((sourceKPGL2ProductEquiv K).symm (a,b)) =
      sourceKPArchMatrixHeight K hζ a * sourceKPFiniteMatrixHeightProduct K b := by
  rw [sourceKPAdelicHeight_product]
  congr 1
  · apply Finset.prod_congr rfl
    intro v _
    change sourceArchHeight (sourceKPArchMatrixComplexEquiv K hζ v
      (sourceArchGLPiEquiv K ((sourceKPGL2ProductEquiv K)
        ((sourceKPGL2ProductEquiv K).symm (a,b))).1 v)) ^ v.mult = _
    rw [MulEquiv.apply_symm_apply]
  · apply finprod_congr
    intro P
    change sourceKPFiniteMatrixHeight K P (sourceKPAdeleMatrixAt K P
      ((sourceKPGL2ProductEquiv K) ((sourceKPGL2ProductEquiv K).symm (a,b))).2) = _
    rw [MulEquiv.apply_symm_apply]

theorem sourceKPAdelicProjectiveProductEquiv_mk (g : GL (Fin 2) 𝔸[K]) :
    sourceKPAdelicProjectiveProductEquiv K (ProjGenLinGroup.mk g) =
      (ProjGenLinGroup.mk ((sourceKPGL2ProductEquiv K g).1),
       ProjGenLinGroup.mk ((sourceKPGL2ProductEquiv K g).2)) := rfl

theorem sourceKPAdelicCoverHeight_arch_matrix (b : SourceKPFiniteAdeleProjective K hζ)
    (u : GL (Fin 2) 𝔸ᶠ[K])
    (hu : sourceKPFiniteAdeleProjectiveProjection K hζ b = ProjGenLinGroup.mk u)
    (a : GL (Fin 2) (InfiniteAdeleRing K)) :
    sourceKPAdelicCoverHeight K hζ (ProjGenLinGroup.mk a,b) =
      sourceKPArchMatrixHeight K hζ a * sourceKPFiniteMatrixHeightProduct K u := by
  have hp : sourceKPAdelicProjectiveProjection K hζ (ProjGenLinGroup.mk a,b) =
      ProjGenLinGroup.mk ((sourceKPGL2ProductEquiv K).symm (a,u)) := by
    apply (sourceKPAdelicProjectiveProductEquiv K).injective
    rw [sourceKPAdelicProjectiveProjection_product, sourceKPAdelicProjectiveProductEquiv_mk,
      MulEquiv.apply_symm_apply, hu]
  rw [sourceKPAdelicCoverHeight, hp, sourceKPAdelicHeightOnProjective_mk, sourceKPAdelicHeight_pair]

theorem sourceKPAdelicCoverHeight_arch_continuous (b : SourceKPFiniteAdeleProjective K hζ) :
    Continuous (fun a : PGL(2, InfiniteAdeleRing K) => sourceKPAdelicCoverHeight K hζ (a,b)) := by
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_surjective (sourceKPFiniteAdeleProjectiveProjection K hζ b)
  apply (QuotientGroup.isQuotientMap_mk
    (Subgroup.center (GL (Fin 2) (InfiniteAdeleRing K)))).continuous_iff.mpr
  change Continuous (fun a : GL (Fin 2) (InfiniteAdeleRing K) =>
    sourceKPAdelicCoverHeight K hζ (ProjGenLinGroup.mk a,b))
  exact ((sourceKPArchMatrixHeight_continuous K hζ).mul_const
    (sourceKPFiniteMatrixHeightProduct K u)).congr
      (fun a => (sourceKPAdelicCoverHeight_arch_matrix K hζ b u hu.symm a).symm)

end
end ArtinMatthews
