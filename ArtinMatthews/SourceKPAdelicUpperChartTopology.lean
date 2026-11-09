module

public import ArtinMatthews.SourceKPAdelicArchHeightPaths
public import ArtinMatthews.SourceKPAdelicSectionUpperChart
public import OAI.NumberTheory.DirichletL.Eisenstein.QuotientTopology


set_option backward.privateInPublic true
@[expose] public section

/-! The actual upper-half-space coordinates have continuous adelic
matrix representatives. This supplies compact matrix sets for testing
the rational Eisenstein sum on compact subsets of a chart. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix OAI.CubicEisenstein
open SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

abbrev SourceKPUpperHalf := {p : EuclideanSpatial // 0 < p 2}

def sourceKPUpperCoordinates (p : SourceKPUpperHalf) : UpperCoordinates :=
  ⟨((p.val 0 : ℂ)+(p.val 1 : ℂ)*Complex.I,p.val 2),p.property⟩

theorem sourceKPUpperCoordinates_continuous : Continuous sourceKPUpperCoordinates := by
  apply Continuous.subtype_mk
  apply Continuous.prodMk
  · exact (Complex.continuous_ofReal.comp (by fun_prop)).add
      ((Complex.continuous_ofReal.comp (by fun_prop)).mul_const Complex.I)
  · fun_prop

def sourceKPUpperChartSection (p : SourceKPUpperHalf) : GL (Fin 2) ℂ :=
  (coordinateSection (sourceKPUpperCoordinates p)).toGL

theorem sourceKPUpperChartSection_eq (p : SourceKPUpperHalf) :
    sourceKPUpperChartSection p =
      (upperSection ((p.val 0 : ℂ)+(p.val 1 : ℂ)*Complex.I) (p.val 2) p.property : GL (Fin 2) ℂ) := rfl

theorem sourceKPUpperChartSection_continuous : Continuous sourceKPUpperChartSection :=
  SpecialLinearGroup.continuous_toGL.comp
    (continuous_coordinateSection.comp sourceKPUpperCoordinates_continuous)

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAdelicArchSingleMatrix (v : InfinitePlace K) (a : GL (Fin 2) ℂ) : GL (Fin 2) 𝔸[K] :=
  (sourceKPGL2ProductEquiv K).symm (sourceArchMatrixSingle K hζ v a,1)

theorem sourceKPAdelicArchSingleMatrix_continuous (v : InfinitePlace K) :
    Continuous (sourceKPAdelicArchSingleMatrix K hζ v) :=
  (sourceKPGL2ProductEquiv_symm_continuous K).comp
    ((sourceKPCutoffArchMatrixSingle_continuous K hζ v).prodMk continuous_const)

theorem sourceKPAdelicArchSingleMatrix_projection (v : InfinitePlace K) (a : GL (Fin 2) ℂ) :
    sourceKPAdelicProjectiveProjection K hζ (sourceArchGroupSingle K hζ v a) =
      ProjGenLinGroup.mk (sourceKPAdelicArchSingleMatrix K hζ v a) := by
  apply (sourceKPAdelicProjectiveProductEquiv K).injective
  rw [sourceKPAdelicProjectiveProjection_product, sourceKPAdelicProjectiveProductEquiv_mk,
    sourceKPAdelicArchSingleMatrix, MulEquiv.apply_symm_apply]
  change (ProjGenLinGroup.mk (sourceArchMatrixSingle K hζ v a),
    sourceKPFiniteAdeleProjectiveProjection K hζ 1) =
      (ProjGenLinGroup.mk (sourceArchMatrixSingle K hζ v a),ProjGenLinGroup.mk 1)
  rw [map_one,map_one]

def sourceKPAdelicUpperChartMatrix (g : GL (Fin 2) 𝔸[K]) (v : InfinitePlace K)
    (p : SourceKPUpperHalf) : GL (Fin 2) 𝔸[K] :=
  g*sourceKPAdelicArchSingleMatrix K hζ v (sourceKPUpperChartSection p)

theorem sourceKPAdelicUpperChartMatrix_continuous (g : GL (Fin 2) 𝔸[K]) (v : InfinitePlace K) :
    Continuous (sourceKPAdelicUpperChartMatrix K hζ g v) :=
  continuous_const.mul ((sourceKPAdelicArchSingleMatrix_continuous K hζ v).comp
    sourceKPUpperChartSection_continuous)

theorem sourceKPAdelicUpperChartMatrix_projection (q : SourceKPAdelicProjective K hζ)
    (g : GL (Fin 2) 𝔸[K]) (hg : sourceKPAdelicProjectiveProjection K hζ q = ProjGenLinGroup.mk g)
    (v : InfinitePlace K) (p : SourceKPUpperHalf) :
    sourceKPAdelicProjectiveProjection K hζ
      (q*sourceArchGroupSingle K hζ v (sourceKPUpperChartSection p)) =
        ProjGenLinGroup.mk (sourceKPAdelicUpperChartMatrix K hζ g v p) := by
  rw [map_mul,hg,sourceKPAdelicArchSingleMatrix_projection,← map_mul]
  rfl

end
end ArtinMatthews
