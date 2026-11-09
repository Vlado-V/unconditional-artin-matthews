module

public import ArtinMatthews.SourceArchMobiusDifferential
public import ArtinMatthews.SourceHyperbolicEnergy


set_option backward.privateInPublic true
@[expose] public section

/-! The exact hyperbolic Dirichlet integrand under a genuine Mobius action. -/
namespace ArtinMatthews.SourceArchJacquet
open OAI.CubicEisenstein SourceHyperbolicGreen
open scoped BigOperators
noncomputable section

lemma sourceArch_coordinateVector_basis (j : Fin 3) :
    euclideanCoordinateVector j = EuclideanSpace.basisFun (Fin 3) ℝ j := by
  rw [EuclideanSpace.basisFun_apply]
  rfl

lemma sourceArch_similarity_gradientEnergy (A : EuclideanSpatial → EuclideanSpatial)
    (p : EuclideanSpatial) (r : ℝ) (e : EuclideanSpatial ≃ₗᵢ[ℝ] EuclideanSpatial)
    (hA : HasFDerivAt A (r • e.toContinuousLinearEquiv.toContinuousLinearMap) p)
    (hY : A p 2 = r * p 2) (f : EuclideanSpatial → ℂ)
    (hf : DifferentiableAt ℝ f (A p)) :
    gradientEnergy (f ∘ A) p = gradientEnergy f (A p) := by
  have hd := (hf.hasFDerivAt.comp p hA).fderiv
  unfold gradientEnergy coordinatePartial
  rw [hd]
  simp only [ContinuousLinearMap.comp_apply]
  simp_rw [sourceArch_coordinateVector_basis]
  rw [sourceArch_scaled_orthonormal_gradient_square, hY]
  ring

theorem sourceArchMobiusEuclidean_gradientEnergy (g : Matrix.SpecialLinearGroup (Fin 2) ℂ)
    (f : EuclideanSpatial → ℂ) (p : EuclideanSpatial) (hp : 0 < p 2)
    (hf : DifferentiableAt ℝ f (sourceArchMobiusEuclidean g p)) :
    gradientEnergy (f ∘ sourceArchMobiusEuclidean g) p =
      gradientEnergy f (sourceArchMobiusEuclidean g p) := by
  obtain ⟨r, e, _hr, hD, hY⟩ := sourceArchMobiusEuclidean_isometric_differential g p hp
  exact sourceArch_similarity_gradientEnergy _ p r e hD hY f hf

end
end ArtinMatthews.SourceArchJacquet
