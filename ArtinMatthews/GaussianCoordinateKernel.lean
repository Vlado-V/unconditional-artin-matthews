module

public import ArtinMatthews.GaussianCoordinatePhase
public import ArtinMatthews.GaussianCoordinateProduct


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Finset
noncomputable section
variable {β : Type*} [Fintype β]

def coordinateGaussianKernel (a : ℝ) (ξ : β → ℝ) : ℂ :=
  ∑' n : β → ℤ, (coordinateGaussianWeight a n:ℂ)*coordinatePhase ξ n

def coordinatePeriodizedGaussian (t : ℝ) (ξ : β → ℝ) : ℝ :=
  ∑' m : β → ℤ, Real.exp (-t*∑ i, ((m i:ℝ)-ξ i)^2)

theorem coordinate_weighted_phase_summable {a : ℝ} (ha : 0 < a) (ξ : β → ℝ) :
    Summable (fun n : β → ℤ => (coordinateGaussianWeight a n:ℂ)*coordinatePhase ξ n) := by
  simp_rw [coordinateGaussianWeight_phase]
  exact GaussianCoordinateProduct.complex_summable_prod _ (fun i => summable_norm_coordinateGaussianFactor ha (ξ i))

theorem coordinateGaussianKernel_poisson {a : ℝ} (ha : 0 < a) (ξ : β → ℝ) :
    coordinateGaussianKernel a ξ =
      (((1/Real.sqrt a)^(Fintype.card β):ℝ):ℂ)*(coordinatePeriodizedGaussian (Real.pi/a) ξ:ℂ) := by
  have hdual (i : β) : Summable (fun m : ℤ =>
      ‖Complex.exp ((-Real.pi/a*((m:ℝ)-ξ i)^2:ℝ):ℂ)‖) := by
    simp only [Complex.norm_exp,Complex.ofReal_re]
    simpa only [div_eq_mul_inv,mul_assoc] using coordinate_summable_real_gaussian_shift (inv_pos.mpr ha) (ξ i)
  unfold coordinateGaussianKernel
  simp_rw [coordinateGaussianWeight_phase]
  rw [GaussianCoordinateProduct.complex_tsum_prod _ (fun i => summable_norm_coordinateGaussianFactor ha (ξ i))]
  simp_rw [show ∀ i : β, (∑' n : ℤ, coordinateGaussianFactor a (ξ i) n) =
      ((1/Real.sqrt a:ℝ):ℂ)*(∑' m : ℤ, Complex.exp ((-Real.pi/a*((m:ℝ)-ξ i)^2:ℝ):ℂ)) from
      fun i => coordinate_gaussian_poisson ha (ξ i)]
  rw [prod_mul_distrib,prod_const,card_univ,← GaussianCoordinateProduct.complex_tsum_prod _ hdual]
  rw [Complex.ofReal_pow]
  congr 1
  unfold coordinatePeriodizedGaussian
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro m
  rw [← Complex.exp_sum,Complex.ofReal_exp]
  congr 1
  push_cast
  simp only [mul_sum,neg_div]

theorem coordinatePeriodizedGaussian_nonneg (t : ℝ) (ξ : β → ℝ) :
    0 ≤ coordinatePeriodizedGaussian t ξ := tsum_nonneg (fun _ => (Real.exp_pos _).le)

theorem coordinateGaussianKernel_norm {a : ℝ} (ha : 0 < a) (ξ : β → ℝ) :
    ‖coordinateGaussianKernel a ξ‖ =
      (1/Real.sqrt a)^(Fintype.card β)*coordinatePeriodizedGaussian (Real.pi/a) ξ := by
  rw [coordinateGaussianKernel_poisson ha,norm_mul,Complex.norm_real,Complex.norm_real,
    Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (by positivity),
    abs_of_nonneg (coordinatePeriodizedGaussian_nonneg _ _)]

theorem coordinateGaussianKernel_neg (a : ℝ) (ξ : β → ℝ) :
    coordinateGaussianKernel a (-ξ) = star (coordinateGaussianKernel a ξ) := by
  unfold coordinateGaussianKernel
  rw [tsum_star]
  apply tsum_congr
  intro n
  rw [coordinatePhase_neg,star_mul']
  simp only [Complex.star_def,Complex.conj_ofReal]

theorem coordinateGaussianKernel_norm_sub_symm (a : ℝ) (ξ η : β → ℝ) :
    ‖coordinateGaussianKernel a (ξ-η)‖ = ‖coordinateGaussianKernel a (η-ξ)‖ := by
  rw [show η-ξ = -(ξ-η) by abel,coordinateGaussianKernel_neg,norm_star]

end
end ArtinMatthews
