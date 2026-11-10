module

public import ArtinMatthews.SourceHyperbolicProductGreen
public import ArtinMatthews.SourceArchProductCasimir
public import Mathlib.Analysis.Calculus.FDeriv.Pi


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceHyperbolicGreen
open OAI.CubicEisenstein MeasureTheory Filter
open scoped Topology ContDiff BigOperators Classical
noncomputable section

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem update_mem_productUpper {p : ProductSpace ι} (hp : p ∈ productUpper ι)
    (i : ι) {q : EuclideanSpatial} (hq : q ∈ euclideanUpperHalf) :
    Function.update p i q ∈ productUpper ι := by
  intro k _
  by_cases hk : k=i
  · subst k
    simpa only [Function.update_self] using hq
  · simpa only [Function.update_of_ne hk, euclideanUpperHalf, Set.mem_ofPred_eq] using productUpper_pos hp k

theorem coordinatePartial_slice {f : ProductSpace ι → ℂ} (p : ProductSpace ι)
    (i : ι) (j : Fin 3) (q : EuclideanSpatial)
    (hf : DifferentiableAt ℝ f (Function.update p i q)) :
    coordinatePartial (fun y => f (Function.update p i y)) j q =
      productPartial f i j (Function.update p i q) := by
  have hu := hasFDerivAt_update (𝕜 := ℝ) p (i := i) q
  unfold coordinatePartial productPartial
  change (fderiv ℝ (f ∘ Function.update p i) q) (euclideanCoordinateVector j) = _
  rw [fderiv_comp q hf hu.differentiableAt, hu.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  congr 1
  ext k
  by_cases hk : k=i
  · subst k
    simp [productDirection]
  · simp [productDirection, hk]

theorem coordinatePartial_slice_second {f : ProductSpace ι → ℂ} {p : ProductSpace ι}
    (hf : ∀ q ∈ productUpper ι, ContDiffAt ℝ 2 f q) (hp : p ∈ productUpper ι)
    (i : ι) (j : Fin 3) :
    coordinatePartial (coordinatePartial (fun y => f (Function.update p i y)) j) j (p i) =
      productPartial (productPartial f i j) i j p := by
  have he : (coordinatePartial (fun y => f (Function.update p i y)) j) =ᶠ[𝓝 (p i)]
      (fun y => productPartial f i j (Function.update p i y)) := by
    filter_upwards [upperHalf_isOpen.mem_nhds (productUpper_pos hp i)] with y hy
    exact coordinatePartial_slice p i j y
      ((hf _ (update_mem_productUpper hp i hy)).differentiableAt (by norm_num))
  calc
    _ = coordinatePartial (fun y => productPartial f i j (Function.update p i y)) j (p i) :=
      congrArg (fun L => L (euclideanCoordinateVector j)) (he.fderiv_eq (𝕜 := ℝ))
    _ = _ := by
      have h := coordinatePartial_slice (f := productPartial f i j) p i j (p i)
        (by simpa only [Function.update_eq_self] using
          (productPartial_contDiffAt (hf p hp) i j).differentiableAt (by norm_num))
      simpa only [Function.update_eq_self] using h

theorem blockLaplacian_eq_slice {f : ProductSpace ι → ℂ} {p : ProductSpace ι}
    (hf : ∀ q ∈ productUpper ι, ContDiffAt ℝ 2 f q) (hp : p ∈ productUpper ι) (i : ι) :
    blockLaplacian f i p =
      positiveEuclideanLaplacian (fun y => f (Function.update p i y)) (p i) := by
  have hfirst := coordinatePartial_slice p i 2 (p i)
    (by simpa only [Function.update_eq_self] using (hf p hp).differentiableAt (by norm_num))
  simp only [Function.update_eq_self] at hfirst
  have hsecond (j : Fin 3) := coordinatePartial_slice_second hf hp i j
  change blockLaplacian f i p =
    -(p i 2 : ℂ)^2 * (∑ j : Fin 3,
      coordinatePartial (coordinatePartial (fun y => f (Function.update p i y)) j) j (p i)) +
      (p i 2 : ℂ) * coordinatePartial (fun y => f (Function.update p i y)) 2 (p i)
  simp only [hsecond, hfirst, blockLaplacian]

theorem productLaplacian_eq_native {f : ProductSpace ι → ℂ} {p : ProductSpace ι}
    (hf : ∀ q ∈ productUpper ι, ContDiffAt ℝ 2 f q) (hp : p ∈ productUpper ι) :
    productLaplacian f p = SourceArchJacquet.sourceArchProductCoordinateLaplacian f p := by
  unfold productLaplacian SourceArchJacquet.sourceArchProductCoordinateLaplacian
  exact Finset.sum_congr rfl (fun i _ => blockLaplacian_eq_slice hf hp i)

end
end ArtinMatthews.SourceHyperbolicGreen
