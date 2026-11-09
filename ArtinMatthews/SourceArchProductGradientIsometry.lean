module

public import ArtinMatthews.SourceArchGradientIsometry
public import ArtinMatthews.SourceHyperbolicProductEnergy


set_option backward.privateInPublic true
@[expose] public section

/-! Blockwise similarities preserve the actual product hyperbolic gradient integrand. -/
namespace ArtinMatthews.SourceArchJacquet
open OAI.CubicEisenstein SourceHyperbolicGreen
open scoped BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι]

lemma sourceArch_product_similarity_gradientEnergy
    (A : ι → EuclideanSpatial → EuclideanSpatial) (p : ProductSpace ι)
    (r : ι → ℝ) (e : ι → EuclideanSpatial ≃ₗᵢ[ℝ] EuclideanSpatial)
    (hA : ∀ i, HasFDerivAt (A i) (r i • (e i).toContinuousLinearEquiv.toContinuousLinearMap) (p i))
    (hY : ∀ i, A i (p i) 2 = r i * p i 2)
    (f : ProductSpace ι → ℂ) (hf : DifferentiableAt ℝ f (fun i => A i (p i))) :
    productGradientEnergy (f ∘ (fun q i => A i (q i))) p =
      productGradientEnergy f (fun i => A i (p i)) := by
  classical
  let D : ProductSpace ι →L[ℝ] ProductSpace ι := ContinuousLinearMap.pi
    (fun i => (r i • (e i).toContinuousLinearEquiv.toContinuousLinearMap).comp
      (ContinuousLinearMap.proj i))
  have hdA : HasFDerivAt (fun q i => A i (q i)) D p := by
    rw [hasFDerivAt_pi]
    intro i
    simpa [D, Function.comp_def] using (hA i).comp p
      (ContinuousLinearMap.proj i : ProductSpace ι →L[ℝ] EuclideanSpatial).hasFDerivAt
  have hd := (hf.hasFDerivAt.comp p hdA).fderiv
  unfold productGradientEnergy productPartial
  rw [hd]
  apply Finset.sum_congr rfl
  intro i _hi
  let F : EuclideanSpatial →L[ℝ] ℂ :=
    (fderiv ℝ f (fun k => A k (p k))).comp
      (ContinuousLinearMap.single ℝ (fun _ : ι => EuclideanSpatial) i)
  have hD (j : Fin 3) : D (productDirection i j) =
      ContinuousLinearMap.single ℝ (fun _ : ι => EuclideanSpatial) i
        ((r i • (e i).toContinuousLinearEquiv.toContinuousLinearMap) (euclideanCoordinateVector j)) := by
    ext k
    by_cases hki : k = i
    · subst k
      simp [D, productDirection]
    · simp [D, productDirection, hki]
  simp only [ContinuousLinearMap.comp_apply]
  simp_rw [hD]
  change (p i 2) ^ 2 * ∑ j : Fin 3,
      ‖F ((r i • (e i).toContinuousLinearEquiv.toContinuousLinearMap) (euclideanCoordinateVector j))‖ ^ 2 =
    (A i (p i) 2) ^ 2 * ∑ j : Fin 3, ‖F (euclideanCoordinateVector j)‖ ^ 2
  have hb (j : Fin 3) : euclideanCoordinateVector j = EuclideanSpace.basisFun (Fin 3) ℝ j := by
    rw [EuclideanSpace.basisFun_apply]
    rfl
  simp_rw [hb]
  rw [sourceArch_scaled_orthonormal_gradient_square, hY i]
  ring

end
end ArtinMatthews.SourceArchJacquet
