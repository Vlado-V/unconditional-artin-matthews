module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Fourier.Inversion


set_option backward.privateInPublic true
@[expose] public section

/-! A genuine L1 Fourier pairing, with its complete product-integrable
kernel.  No formal integral of a Fourier character is used. -/

noncomputable section
open MeasureTheory Filter
open scoped FourierTransform

namespace ArtinMatthews

def spectralFourierPairKernel (f H : ℝ → ℂ) (x t : ℝ) : ℂ :=
  Complex.exp (((-2*Real.pi*x*t : ℝ) : ℂ)*Complex.I)*f x*H t

theorem spectralFourierPairKernel_integrable (f H : ℝ → ℂ)
    (hf : Integrable f) (hH : Integrable H) :
    Integrable (fun p : ℝ × ℝ => spectralFourierPairKernel f H p.1 p.2) := by
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => spectralFourierPairKernel f H p.1 p.2) :=
    ((show Continuous (fun p : ℝ × ℝ =>
      Complex.exp (((-2*Real.pi*p.1*p.2 : ℝ) : ℂ)*Complex.I)) by fun_prop).aestronglyMeasurable.mul
        hf.aestronglyMeasurable.comp_fst).mul hH.aestronglyMeasurable.comp_snd
  apply (hf.norm.mul_prod hH.norm).mono' hm
  filter_upwards [] with p
  simp [spectralFourierPairKernel,Complex.norm_exp]

theorem spectralFourierPairKernel_integral_x (f H : ℝ → ℂ) (t : ℝ) :
    (∫ x : ℝ, spectralFourierPairKernel f H x t) = 𝓕 f t * H t := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  exact integral_mul_const _ _

theorem spectralFourierPairKernel_integral_t (f H : ℝ → ℂ) (x : ℝ) :
    (∫ t : ℝ, spectralFourierPairKernel f H x t) = f x * 𝓕 H x := by
  rw [Real.fourier_real_eq_integral_exp_smul,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  unfold spectralFourierPairKernel
  have he : -2*Real.pi*x*t = -2*Real.pi*t*x := by ring
  rw [he]
  simp only [smul_eq_mul]
  ring

theorem spectral_integral_fourier_mul (f H : ℝ → ℂ) (hf : Integrable f) (hH : Integrable H) :
    (∫ t : ℝ, 𝓕 f t * H t) = ∫ x : ℝ, f x * 𝓕 H x := by
  have hI := spectralFourierPairKernel_integrable f H hf hH
  calc
    _ = ∫ t : ℝ, ∫ x : ℝ, spectralFourierPairKernel f H x t := by
      simp only [spectralFourierPairKernel_integral_x]
    _ = ∫ x : ℝ, ∫ t : ℝ, spectralFourierPairKernel f H x t := (integral_integral_swap hI).symm
    _ = _ := by simp only [spectralFourierPairKernel_integral_t]

theorem spectral_fourier_product_pairing (f g : ℝ → ℂ)
    (hf : Integrable f) (hg : Integrable g) (hG : Integrable (𝓕 g)) (hgc : Continuous g) :
    (∫ t : ℝ, 𝓕 f t * 𝓕 g t) = ∫ x : ℝ, f x * g (-x) := by
  rw [spectral_integral_fourier_mul f (𝓕 g) hf hG]
  apply integral_congr_ae
  filter_upwards [] with x
  have he := hg.fourierInv_fourier_eq hG (hgc.continuousAt (x := -x))
  rw [Real.fourierInv_eq_fourier_neg,neg_neg] at he
  rw [he]

end ArtinMatthews
