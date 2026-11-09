module

public import ArtinMatthews.SourceComplexZetaIntegrability
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Prod


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.VaryingKummerAnalytic
open MeasureTheory Set
open scoped SchwartzMap
noncomputable section

def sourceComplexZetaGaussianKernel (a : ℝ) (t : ℝ) (z : ℂ) : ℝ :=
  t ^ (a / 2 - 1) * Real.exp (-(‖z‖ ^ 2 * t))

theorem sourceComplexZetaGaussianKernel_nonneg (a t : ℝ) (ht : 0 ≤ t) (z : ℂ) :
    0 ≤ sourceComplexZetaGaussianKernel a t z :=
  mul_nonneg (Real.rpow_nonneg ht _) (Real.exp_nonneg _)

theorem sourceComplexZetaGaussianKernel_integrable (a : ℝ) (ha : 0 < a)
    (z : ℂ) (hz : z ≠ 0) :
    IntegrableOn (fun t => sourceComplexZetaGaussianKernel a t z) (Ioi 0) := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  simpa only [sourceComplexZetaGaussianKernel, Real.rpow_one, neg_mul] using
    integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := a / 2 - 1) (p := 1) (b := ‖z‖ ^ 2)
      (by linarith) (by norm_num) (sq_pos_of_pos hn)

theorem sourceComplexZetaGaussianKernel_integral (a : ℝ) (ha : 0 < a)
    (z : ℂ) (hz : z ≠ 0) :
    (∫ t : ℝ in Ioi 0, sourceComplexZetaGaussianKernel a t z) =
      Real.Gamma (a / 2) * ‖z‖ ^ (-a) :=
  source_complex_gaussian_mellin a ha z hz

theorem sourceComplexZetaGaussianKernel_norm_integral (a : ℝ) (ha : 0 < a)
    (z c : ℂ) (hz : z ≠ 0) :
    (∫ t : ℝ in Ioi 0, ‖c * (sourceComplexZetaGaussianKernel a t z : ℂ)‖) =
      Real.Gamma (a / 2) * ‖c * (‖z‖ ^ (-a) : ℝ)‖ := by
  have he : (∫ t : ℝ in Ioi 0, ‖c * (sourceComplexZetaGaussianKernel a t z : ℂ)‖) =
      ∫ t : ℝ in Ioi 0, ‖c‖ * sourceComplexZetaGaussianKernel a t z := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sourceComplexZetaGaussianKernel_nonneg a t ht.le z)]
  rw [he, integral_const_mul, sourceComplexZetaGaussianKernel_integral a ha z hz,
    norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _)]
  ring

theorem sourceComplexZetaGaussian_integrable (f : 𝓢(ℂ, ℂ)) (a : ℝ)
    (ha : 0 < a) (ha2 : a < 2) :
    Integrable (fun p : ℂ × ℝ => f p.1 * (sourceComplexZetaGaussianKernel a p.2 p.1 : ℂ))
      (volume.prod (volume.restrict (Ioi 0))) := by
  have hm : AEStronglyMeasurable
      (fun p : ℂ × ℝ => f p.1 * (sourceComplexZetaGaussianKernel a p.2 p.1 : ℂ))
      (volume.prod (volume.restrict (Ioi 0))) := by
    apply Measurable.aestronglyMeasurable
    unfold sourceComplexZetaGaussianKernel
    fun_prop
  have hz : ∀ᵐ z : ℂ, z ≠ 0 := by
    apply ae_iff.mpr
    simp
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [hz] with z hz
    exact ((sourceComplexZetaGaussianKernel_integrable a ha z hz).ofReal).const_mul (f z)
  · apply ((source_complex_schwartz_weighted_integrable f a ha.le ha2).norm.const_mul
      (Real.Gamma (a / 2))).congr
    filter_upwards [hz] with z hz
    exact (sourceComplexZetaGaussianKernel_norm_integral a ha z (f z) hz).symm

/-- The weighted local zeta pairing has an actual absolutely convergent
Gaussian Mellin representation; the order of integration is justified. -/
theorem source_complex_zeta_gaussian_representation (f : 𝓢(ℂ, ℂ)) (a : ℝ)
    (ha : 0 < a) (ha2 : a < 2) :
    (Real.Gamma (a / 2) : ℂ) * (∫ z : ℂ, f z * (‖z‖ ^ (-a) : ℝ)) =
      ∫ t : ℝ in Ioi 0, ∫ z : ℂ, f z * (sourceComplexZetaGaussianKernel a t z : ℂ) := by
  have hrep : (∫ z : ℂ, ∫ t : ℝ in Ioi 0, f z * (sourceComplexZetaGaussianKernel a t z : ℂ)) =
      (Real.Gamma (a / 2) : ℂ) * (∫ z : ℂ, f z * (‖z‖ ^ (-a) : ℝ)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    have hz : ∀ᵐ z : ℂ, z ≠ 0 := by apply ae_iff.mpr; simp
    filter_upwards [hz] with z hz
    rw [integral_const_mul, integral_complex_ofReal,
      sourceComplexZetaGaussianKernel_integral a ha z hz, Complex.ofReal_mul]
    ring
  rw [← hrep]
  exact integral_integral_swap (sourceComplexZetaGaussian_integrable f a ha ha2)

end
end ArtinMatthews.VaryingKummerAnalytic
