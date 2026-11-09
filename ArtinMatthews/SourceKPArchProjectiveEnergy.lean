module

public import ArtinMatthews.SourceArchProjectiveEnergy
public import ArtinMatthews.SourceArchProductGradientIsometry
public import ArtinMatthews.SourceKPArchActionSmooth


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine all-place projective action preserves the product Dirichlet form. -/
namespace ArtinMatthews
open NumberField Matrix SourceArchJacquet SourceHyperbolicGreen MeasureTheory Filter
open scoped NumberField MatrixGroups AdeleRing Topology ContDiff
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPArchEuclideanAction_gradientEnergy (a : PGL(2, InfiniteAdeleRing K))
    (f : ProductSpace (InfinitePlace K) → ℂ) (p : ProductSpace (InfinitePlace K))
    (hp : p ∈ productUpper (InfinitePlace K))
    (hf : DifferentiableAt ℝ f (sourceKPArchEuclideanAction K hζ a p)) :
    productGradientEnergy (f ∘ sourceKPArchEuclideanAction K hζ a) p =
      productGradientEnergy f (sourceKPArchEuclideanAction K hζ a p) := by
  classical
  choose r e _hr hD hY using fun v : InfinitePlace K =>
    sourceArchEuclideanProjectiveAction_isometric_differential
      (sourceKPArchProjectiveAt K hζ v a) (p v) (productUpper_pos hp v)
  exact sourceArch_product_similarity_gradientEnergy
    (fun v => sourceArchEuclideanProjectiveAction (sourceKPArchProjectiveAt K hζ v a))
    p r e hD hY f hf

theorem sourceKPArchEuclideanAction_gradientEnergy_ae (a : PGL(2, InfiniteAdeleRing K))
    (f : ProductSpace (InfinitePlace K) → ℂ)
    (hf : ∀ p ∈ productUpper (InfinitePlace K), DifferentiableAt ℝ f p) :
    productGradientEnergy (f ∘ sourceKPArchEuclideanAction K hζ a) =ᵐ[productVolume (InfinitePlace K)]
      (productGradientEnergy f) ∘ sourceKPArchEuclideanAction K hζ a := by
  have hp : ∀ᵐ p ∂productVolume (InfinitePlace K), p ∈ productUpper (InfinitePlace K) := by
    rw [productVolume_eq_density]
    exact (ae_restrict_mem (productUpper_isOpen (InfinitePlace K)).measurableSet).filter_mono
      (withDensity_absolutelyContinuous _ _).ae_le
  have himage (p : ProductSpace (InfinitePlace K)) :
      sourceKPArchEuclideanAction K hζ a p ∈ productUpper (InfinitePlace K) := by
    intro v _hv
    exact sourceArchUpperEuclideanMap_positive _
  filter_upwards [hp] with p hpp
  exact sourceKPArchEuclideanAction_gradientEnergy K hζ a f p hpp (hf _ (himage p))

theorem sourceKPArchEuclideanAction_gradientEnergy_integrable (a : PGL(2, InfiniteAdeleRing K))
    (f : ProductSpace (InfinitePlace K) → ℂ)
    (hf : ∀ p ∈ productUpper (InfinitePlace K), DifferentiableAt ℝ f p)
    (hE : Integrable (productGradientEnergy f) (productVolume (InfinitePlace K))) :
    Integrable (productGradientEnergy (f ∘ sourceKPArchEuclideanAction K hζ a))
      (productVolume (InfinitePlace K)) :=
  ((sourceKPArchEuclideanAction_preserving K hζ a).integrable_comp_of_integrable hE).congr
    (sourceKPArchEuclideanAction_gradientEnergy_ae K hζ a f hf).symm

theorem sourceKPArchEuclideanAction_dirichlet (a : PGL(2, InfiniteAdeleRing K))
    (f : ProductSpace (InfinitePlace K) → ℂ)
    (hf : ∀ p ∈ productUpper (InfinitePlace K), DifferentiableAt ℝ f p)
    (hE : Integrable (productGradientEnergy f) (productVolume (InfinitePlace K))) :
    (∫ p, productGradientEnergy (f ∘ sourceKPArchEuclideanAction K hζ a) p
      ∂productVolume (InfinitePlace K)) =
      ∫ p, productGradientEnergy f p ∂productVolume (InfinitePlace K) := by
  have he := sourceKPArchEuclideanAction_gradientEnergy_ae K hζ a f hf
  rw [integral_congr_ae he]
  have hm := sourceKPArchEuclideanAction_preserving K hζ a
  have hmeas : AEStronglyMeasurable (productGradientEnergy f)
      (Measure.map (sourceKPArchEuclideanAction K hζ a) (productVolume (InfinitePlace K))) := by
    rw [hm.map_eq]
    exact hE.aestronglyMeasurable
  simpa only [hm.map_eq, Function.comp_apply] using (integral_map hm.aemeasurable hmeas).symm

theorem sourceKPArchEuclideanAction_dirichlet_core (a : PGL(2, InfiniteAdeleRing K))
    (f : ProductSpace (InfinitePlace K) → ℂ) (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ productUpper (InfinitePlace K)) :
    (∫ p, productGradientEnergy (f ∘ sourceKPArchEuclideanAction K hζ a) p
      ∂productVolume (InfinitePlace K)) =
      ∫ p, productGradientEnergy f p ∂productVolume (InfinitePlace K) :=
  sourceKPArchEuclideanAction_dirichlet K hζ a f
    (fun _ _ => hf.contDiffAt.differentiableAt (by norm_num)) (productGradientEnergy_integrable hf hc hs)

end
end ArtinMatthews
