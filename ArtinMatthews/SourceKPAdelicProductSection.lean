module

public import ArtinMatthews.SourceKPArchTranslatedProduct
public import ArtinMatthews.SourceArchSphericalProductCasimir
public import ArtinMatthews.SourceArchSectionFactorization


set_option backward.privateInPublic true
@[expose] public section

/-! The actual adelic spherical section in a full product of
upper-half-space charts, with its arbitrary finite component retained. -/

namespace ArtinMatthews
open NumberField Matrix OAI.CubicEisenstein Filter
open SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing BigOperators ContDiff Topology Classical
noncomputable section

private theorem productLaplacian_congr {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f g : (ι → EuclideanSpatial) → ℂ) (p : ι → EuclideanSpatial)
    (he : f =ᶠ[𝓝 p] g) :
    sourceArchProductCoordinateLaplacian f p = sourceArchProductCoordinateLaplacian g p := by
  apply Finset.sum_congr rfl
  intro v _
  apply positiveEuclideanLaplacian_congr
  have hc : Continuous (fun q : EuclideanSpatial => Function.update p v q) := by
    apply continuous_pi
    intro w
    by_cases hw : w=v
    · subst w
      simpa only [Function.update_self] using continuous_id'
    · simpa only [Function.update_of_ne hw] using continuous_const
  have ht : Tendsto (fun q : EuclideanSpatial => Function.update p v q) (𝓝 (p v)) (𝓝 p) := by
    simpa only [Function.update_eq_self] using hc.tendsto (p v)
  exact ht.eventually he

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAdelicProductSection (s : ℂ) (q : SourceKPAdelicProjective K hζ)
    (p : InfinitePlace K → EuclideanSpatial) : ℂ :=
  if hp : ∀ v, 0 < p v 2 then sourceKPAdelicCompactScalar K hζ s
    (q*(ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ p hp),1)) else 0

theorem sourceKPAdelicProductSection_factor (s : ℂ)
    (g : GL (Fin 2) (InfiniteAdeleRing K)) (qf : SourceKPFiniteAdeleProjective K hζ)
    (p : InfinitePlace K → EuclideanSpatial) (hp : ∀ v, 0 < p v 2) :
    sourceKPAdelicProductSection K hζ s (ProjGenLinGroup.mk g,qf) p =
      sourceArchTranslatedCoordinateProduct s
        (fun v => sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v)) p *
          sourceKPAdelicCompactScalar K hζ s (1,qf) := by
  rw [sourceKPAdelicProductSection,dite_eq_left hp]
  change sourceKPAdelicCompactScalar K hζ s
    (ProjGenLinGroup.mk g*ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ p hp),qf*1) = _
  rw [mul_one,← map_mul,sourceArchCompactScalar_factor_matrix]
  simp only [map_mul,Pi.mul_apply,sourceArchUpperHalfspaceMatrix,MulEquiv.apply_symm_apply]
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  exact sourceArchTranslatedProfile_eq_section s
    (sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v)) (p v) (hp v)

theorem sourceKPAdelicProductSection_eventually_factor (s : ℂ)
    (g : GL (Fin 2) (InfiniteAdeleRing K)) (qf : SourceKPFiniteAdeleProjective K hζ)
    (p : InfinitePlace K → EuclideanSpatial) (hp : ∀ v, 0 < p v 2) :
    sourceKPAdelicProductSection K hζ s (ProjGenLinGroup.mk g,qf) =ᶠ[𝓝 p]
      fun x => sourceArchTranslatedCoordinateProduct s
        (fun v => sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v)) x *
          sourceKPAdelicCompactScalar K hζ s (1,qf) := by
  have hpos : ∀ᶠ x : InfinitePlace K → EuclideanSpatial in 𝓝 p, ∀ v, 0 < x v 2 := by
    rw [Filter.eventually_all]
    intro v
    have hproj : Continuous (fun y : EuclideanSpatial => y 2) := (EuclideanSpace.proj 2).continuous
    exact (hproj.comp (_root_.continuous_apply v)).continuousAt.eventually_const_lt (hp v)
  filter_upwards [hpos] with x hx
  exact sourceKPAdelicProductSection_factor K hζ s g qf x hx

theorem sourceKPAdelicProductSection_contDiffAt (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (p : InfinitePlace K → EuclideanSpatial)
    (hp : ∀ v, 0 < p v 2) :
    ContDiffAt (ℝ) (∞ : ℕ∞ω) (sourceKPAdelicProductSection K hζ s q) p := by
  rcases q with ⟨a,qf⟩
  obtain ⟨g,rfl⟩ := ProjGenLinGroup.mk_surjective a
  have h := (sourceArchTranslatedCoordinateProduct_contDiffAt s
    (fun v => sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v)) p hp).mul
      (contDiffAt_const (c := sourceKPAdelicCompactScalar K hζ s (1,qf)))
  exact h.congr_of_eventuallyEq (sourceKPAdelicProductSection_eventually_factor K hζ s g qf p hp)

theorem sourceKPAdelicProductSection_laplacian (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (p : InfinitePlace K → EuclideanSpatial)
    (hp : ∀ v, 0 < p v 2) :
    sourceArchProductCoordinateLaplacian (sourceKPAdelicProductSection K hζ s q) p =
      (InfinitePlace.nrComplexPlaces K : ℂ)*(1-4*s^2)*sourceKPAdelicProductSection K hζ s q p := by
  have := source_isTotallyComplex K hζ
  have hcard : Fintype.card (InfinitePlace K) = InfinitePlace.nrComplexPlaces K := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,IsTotallyComplex.nrRealPlaces_eq_zero,zero_add]
  rcases q with ⟨a,qf⟩
  obtain ⟨g,rfl⟩ := ProjGenLinGroup.mk_surjective a
  have he := sourceKPAdelicProductSection_eventually_factor K hζ s g qf p hp
  rw [productLaplacian_congr _ _ p he]
  have hc : (fun x => sourceArchTranslatedCoordinateProduct s
      (fun v => sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v)) x *
        sourceKPAdelicCompactScalar K hζ s (1,qf)) =
      fun x => sourceKPAdelicCompactScalar K hζ s (1,qf) * sourceArchTranslatedCoordinateProduct s
        (fun v => sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v)) x := by
    funext x
    exact mul_comm _ _
  rw [hc,sourceArchTranslatedCoordinateProduct_laplacian s _ _ p hp,hcard,he.eq_of_nhds]
  ring

end
end ArtinMatthews
