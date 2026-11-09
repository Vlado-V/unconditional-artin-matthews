module

public import ArtinMatthews.SourceComplexZetaGaussian
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.MellinTransform


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.VaryingKummerAnalytic
open MeasureTheory Set
open scoped SchwartzMap FourierTransform RealInnerProductSpace
noncomputable section

def sourceComplexGaussianPairing (f : ℂ → ℂ) (t : ℝ) : ℂ :=
  ∫ z : ℂ, f z * (Real.exp (-t * ‖z‖ ^ 2) : ℂ)

private theorem real_gaussian_coe (t : ℝ) :
    (fun z : ℂ => (Real.exp (-t * ‖z‖ ^ 2) : ℂ)) =
      (fun z : ℂ => Complex.exp (-(t : ℂ) * ‖z‖ ^ 2)) := by
  ext z
  push_cast
  rfl

theorem source_complex_gaussian_fourier (t : ℝ) (ht : 0 < t) (z : ℂ) :
    𝓕 (fun x : ℂ => (Real.exp (-t * ‖x‖ ^ 2) : ℂ)) z =
      (Real.pi / t : ℝ) * (Real.exp (-(Real.pi ^ 2 / t) * ‖z‖ ^ 2) : ℂ) := by
  rw [real_gaussian_coe, fourier_gaussian_innerProductSpace (by simpa using ht)]
  norm_num only [Complex.finrank_real_complex, Nat.cast_ofNat, div_self (by norm_num : (2 : ℂ) ≠ 0),
    Complex.cpow_one]
  push_cast
  congr 2
  ring

theorem source_complex_gaussian_pairing_fourier (f : 𝓢(ℂ, ℂ))
    (t : ℝ) (ht : 0 < t) :
    sourceComplexGaussianPairing (𝓕 f : 𝓢(ℂ, ℂ)) t =
      (Real.pi / t : ℝ) * sourceComplexGaussianPairing f (Real.pi ^ 2 / t) := by
  let g : ℂ → ℂ := fun z => (Real.exp (-t * ‖z‖ ^ 2) : ℂ)
  have hg : Integrable g := by
    have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (V := ℂ) (b := (t : ℂ)) (by simpa using ht) 0 0
    rw [show g = _ from real_gaussian_coe t]
    simpa only [zero_mul, add_zero] using h
  have h : (∫ z : ℂ, (𝓕 f : 𝓢(ℂ, ℂ)) z * g z) =
      ∫ z : ℂ, f z * 𝓕 g z := by
    simpa using! VectorFourier.integral_bilin_fourierIntegral_eq_flip
      (ContinuousLinearMap.mul ℂ ℂ) (L := innerₗ ℂ)
      Real.continuous_fourierChar continuous_inner f.integrable hg
  change (∫ z : ℂ, (𝓕 f : 𝓢(ℂ, ℂ)) z * g z) = _
  rw [h]
  simp_rw [show g = (fun z : ℂ => (Real.exp (-t * ‖z‖ ^ 2) : ℂ)) from rfl,
    source_complex_gaussian_fourier t ht, ← mul_assoc,
    mul_comm (f _) ((Real.pi / t : ℝ) : ℂ), mul_assoc]
  rw [integral_const_mul]
  rfl

theorem source_complex_zeta_gaussian_mellin (f : 𝓢(ℂ, ℂ)) (a : ℝ)
    (ha : 0 < a) (ha2 : a < 2) :
    (Real.Gamma (a / 2) : ℂ) * (∫ z : ℂ, f z * (‖z‖ ^ (-a) : ℝ)) =
      mellin (sourceComplexGaussianPairing f) ((a / 2 : ℝ) : ℂ) := by
  rw [source_complex_zeta_gaussian_representation f a ha ha2]
  unfold mellin
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  have hc : (t : ℂ) ^ (((a / 2 : ℝ) : ℂ) - 1) = (t ^ (a / 2 - 1) : ℝ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.ofReal_cpow ht.le]
  rw [hc]
  unfold sourceComplexZetaGaussianKernel sourceComplexGaussianPairing
  simp only [Complex.ofReal_mul, smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    simp only [mul_comm (‖z‖ ^ 2) t, neg_mul]
    ring

end
end ArtinMatthews.VaryingKummerAnalytic
