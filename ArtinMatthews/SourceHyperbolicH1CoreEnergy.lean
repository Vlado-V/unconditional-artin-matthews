module

public import ArtinMatthews.SourceHyperbolicH1EnergyGraph


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceHyperbolicGreen
open OAI.CubicEisenstein MeasureTheory
open scoped Topology ContDiff BigOperators Classical InnerProductSpace
noncomputable section

variable {ι : Type*} [Fintype ι]

theorem h1GradientAt_norm_sq (f : h1Tests ι 2) (p : ProductSpace ι) :
    ‖h1GradientAt f p‖^2 = productGradientEnergy f.val p := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [h1GradientAt,WithLp.ofLp_toLp,Fintype.sum_prod_type,norm_mul,mul_pow,
    Complex.norm_real,Real.norm_eq_abs,sq_abs,productGradientEnergy,Finset.mul_sum]

theorem h1TestGradient_norm_sq (f : h1Tests ι 2) :
    ‖h1TestGradient f‖^2 = ∫ p, productGradientEnergy f.val p ∂productVolume ι := by
  have he : inner ℂ (h1TestGradient f) (h1TestGradient f) =
      (∫ p, productGradientEnergy f.val p ∂productVolume ι : ℝ) := by
    rw [L2.inner_def,← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [h1TestGradient_coe f] with p hp
    rw [hp,inner_self_eq_norm_sq_to_K,RCLike.ofReal_eq_complex_ofReal,
      ← Complex.ofReal_pow,h1GradientAt_norm_sq]
  rw [inner_self_eq_norm_sq_to_K,RCLike.ofReal_eq_complex_ofReal,← Complex.ofReal_pow] at he
  exact Complex.ofReal_injective he

theorem h1DirichletEnergy_core (f : h1Tests ι 2) :
    h1DirichletEnergy (h1EnergyCore f) =
      ∫ p, productGradientEnergy f.val p ∂productVolume ι :=
  h1TestGradient_norm_sq f

theorem h1EnergyCore_green (f : h1Tests ι 2) :
    (∫ p, star (f.val p) * productLaplacian f.val p ∂productVolume ι) =
      (h1DirichletEnergy (h1EnergyCore f) : ℂ) := by
  rw [h1DirichletEnergy_core]
  exact product_green_energy f.prop.1 f.prop.2.1 f.prop.2.2

end
end ArtinMatthews.SourceHyperbolicGreen
