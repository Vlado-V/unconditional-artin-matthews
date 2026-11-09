module

public import ArtinMatthews.SourceKPAdelicProductChartTopology
public import ArtinMatthews.SourceKPAdelicHeightUpperChart


set_option backward.privateInPublic true
@[expose] public section

/-! The actual height in all upper-half-space coordinates, with the
finite matrix height factor retained. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix OAI.CubicEisenstein Filter SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing BigOperators ContDiff Topology Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPProductUpper_eventually (p : InfinitePlace K → EuclideanSpatial)
    (hp : ∀ v, 0 < p v 2) : ∀ᶠ x : InfinitePlace K → EuclideanSpatial in 𝓝 p,
      ∀ v, 0 < x v 2 := by
  rw [Filter.eventually_all]
  intro v
  have hproj : Continuous (fun y : EuclideanSpatial => y 2) := (EuclideanSpace.proj 2).continuous
  exact (hproj.comp (_root_.continuous_apply v)).continuousAt.eventually_const_lt (hp v)

def sourceKPAdelicProductHeight (q : SourceKPAdelicProjective K hζ)
    (p : InfinitePlace K → EuclideanSpatial) : ℝ :=
  if hp : ∀ v, 0 < p v 2 then sourceKPAdelicCoverHeight K hζ
    (q*(ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ p hp),1)) else 0

theorem sourceKPAdelicProductHeight_factor
    (g : GL (Fin 2) (InfiniteAdeleRing K)) (qf : SourceKPFiniteAdeleProjective K hζ)
    (u : GL (Fin 2) 𝔸ᶠ[K])
    (hu : sourceKPFiniteAdeleProjectiveProjection K hζ qf = ProjGenLinGroup.mk u)
    (p : InfinitePlace K → EuclideanSpatial) (hp : ∀ v, 0 < p v 2) :
    sourceKPAdelicProductHeight K hζ (ProjGenLinGroup.mk g,qf) p =
      (∏ v, (sourceArchTranslatedSectionChart 0
        (sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v)) (p v)).re^v.mult)*
          sourceKPFiniteMatrixHeightProduct K u := by
  rw [sourceKPAdelicProductHeight,dite_eq_left hp]
  change sourceKPAdelicCoverHeight K hζ
    (ProjGenLinGroup.mk g*ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ p hp),qf*1) = _
  rw [mul_one,← map_mul,sourceKPAdelicCoverHeight_arch_matrix K hζ qf u hu]
  unfold sourceKPArchMatrixHeight
  simp only [map_mul,Pi.mul_apply,sourceArchUpperHalfspaceMatrix,MulEquiv.apply_symm_apply]
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  simp only [sourceArchTranslatedSectionChart,dite_eq_left (hp v),sourceArchSphericalGL,
    mul_zero,zero_add,Complex.cpow_one,Complex.ofReal_re]

theorem sourceKPAdelicProductHeight_contDiffAt (q : SourceKPAdelicProjective K hζ)
    (p : InfinitePlace K → EuclideanSpatial) (hp : ∀ v, 0 < p v 2) :
    ContDiffAt ℝ (∞ : ℕ∞ω) (sourceKPAdelicProductHeight K hζ q) p := by
  rcases q with ⟨a,qf⟩
  obtain ⟨g,rfl⟩ := ProjGenLinGroup.mk_surjective a
  obtain ⟨u,hu⟩ := ProjGenLinGroup.mk_surjective (sourceKPFiniteAdeleProjectiveProjection K hζ qf)
  let localMatrix := fun v => sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v)
  have hprod : ContDiffAt ℝ (∞ : ℕ∞ω) (fun x : InfinitePlace K → EuclideanSpatial =>
      ∏ v, (sourceArchTranslatedSectionChart 0 (localMatrix v) (x v)).re^v.mult) p := by
    apply contDiffAt_prod
    intro v _
    have hr : ContDiffAt ℝ (∞ : ℕ∞ω)
        (fun r => (sourceArchTranslatedSectionChart 0 (localMatrix v) r).re) (p v) :=
      Complex.reCLM.contDiff.contDiffAt.comp (p v)
        (sourceArchTranslatedSectionChart_contDiffAt 0 (localMatrix v) (p v) (hp v))
    have hev : ContDiffAt ℝ (∞ : ℕ∞ω) (fun x : InfinitePlace K → EuclideanSpatial => x v) p := by
      fun_prop
    exact (hr.comp p hev).pow v.mult
  apply (hprod.mul (contDiffAt_const (c := sourceKPFiniteMatrixHeightProduct K u))).congr_of_eventuallyEq
  filter_upwards [sourceKPProductUpper_eventually K p hp] with x hx
  exact sourceKPAdelicProductHeight_factor K hζ g qf u hu.symm x hx

end
end ArtinMatthews
