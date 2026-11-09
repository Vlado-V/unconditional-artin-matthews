module

public import ArtinMatthews.SpectralWeylContourEstimate
public import ArtinMatthews.SpectralWeylKLNormalization
public import ArtinMatthews.SpectralWeylWindowBaseDecay


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory Complex
noncomputable section

theorem spectralWeylJGaussian_small_of_base
    (H base : ℂ → ℂ) (hEven : ∀ z : ℂ, H (-z) = H z)
    (hFactor : ∀ z : ℂ, H z = base z*spectralABLCoshCancellation z)
    (hHol : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ 5/8 → DifferentiableAt ℂ H z)
    {B : ℝ} (hB : 0 < B)
    (hBase : ∀ t y : ℝ, 0 ≤ y → y ≤ 5/8 →
      ‖base ((t : ℂ)+(y : ℂ)*I)‖ ≤ B/(1+t^2)^2)
    {X₀ : ℝ} (hX₀ : 0 < X₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ R X : ℝ, 1 ≤ R → 0 < X → X ≤ X₀ →
      ‖∫ t : ℝ, spectralWeylJMultiplier t X*H (t : ℂ)*
        Complex.exp (-2*((t : ℂ)/(R : ℂ))^2) ∂spectralKLSpectralMeasure‖ ≤ C*X^(1/4 : ℝ) := by
  let cylinder := fun (ν : ℂ) (x : ℝ) => Complex.besselJ ν (x : ℂ)
  have hCylinder : ∀ X : ℝ, 0 < X → ∀ ν : ℂ, 0 ≤ ν.re →
      ‖cylinder ν X‖ ≤ (X/2)^ν.re*Real.exp (X^2/4)/‖Complex.Gamma (ν+1)‖ := by
    intro X hX ν hν
    exact spectral_besselJ_norm_le_exp_of_re_nonneg ν hν hX
  have hContour : ∀ R X : ℝ, 1 ≤ R → 0 < X → ∀ z : ℂ, 0 ≤ z.im → z.im ≤ 5/8 →
      DifferentiableAt ℂ (spectralWeylContourIntegrand cylinder H R X) z := by
    intro R X _ hX z hz0 hz1
    exact spectralWeylJContour_differentiableAt H R hX hz0 (hHol z hz0 hz1)
  obtain ⟨C,hC,hbound⟩ := spectralWeylContour_normalized_small_bound cylinder H base hFactor
    hCylinder hB hBase hContour hX₀
  refine ⟨C,hC,?_⟩
  intro R X hR hX hXX
  have hint := spectralWeylContour_integrable_line cylinder H base hFactor hCylinder hB hBase
    hR hX (hContour R X hR hX) (y:=0) (by norm_num) (by norm_num)
  simp only [Complex.ofReal_zero,zero_mul,add_zero] at hint
  rw [(spectralWeylJGaussian_eq_contour H hEven R hX hint).2]
  exact hbound R X hR hX hXX

theorem spectralWeylKGaussian_small_of_base
    (H base : ℂ → ℂ) (hEven : ∀ z : ℂ, H (-z) = H z)
    (hFactor : ∀ z : ℂ, H z = base z*spectralABLCoshCancellation z)
    (hHol : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ 5/8 → DifferentiableAt ℂ H z)
    {B : ℝ} (hB : 0 < B)
    (hBase : ∀ t y : ℝ, 0 ≤ y → y ≤ 5/8 →
      ‖base ((t : ℂ)+(y : ℂ)*I)‖ ≤ B/(1+t^2)^2)
    {X₀ : ℝ} (hX₀ : 0 < X₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ R X : ℝ, 1 ≤ R → 0 < X → X ≤ X₀ →
      ‖∫ t : ℝ, spectralWeylKMultiplier t X*H (t : ℂ)*
        Complex.exp (-2*((t : ℂ)/(R : ℂ))^2) ∂spectralKLSpectralMeasure‖ ≤ C*X^(1/4 : ℝ) := by
  have hCylinder : ∀ X : ℝ, 0 < X → ∀ ν : ℂ, 0 ≤ ν.re →
      ‖spectralBesselI ν X‖ ≤ (X/2)^ν.re*Real.exp (X^2/4)/‖Complex.Gamma (ν+1)‖ := by
    intro X hX ν hν
    exact spectralBesselI_norm_le_exp_of_re_nonneg ν hν hX
  have hContour : ∀ R X : ℝ, 1 ≤ R → 0 < X → ∀ z : ℂ, 0 ≤ z.im → z.im ≤ 5/8 →
      DifferentiableAt ℂ (spectralWeylContourIntegrand spectralBesselI H R X) z := by
    intro R X _ hX z hz0 hz1
    exact spectralWeylIContour_differentiableAt H R hX hz0 (hHol z hz0 hz1)
  obtain ⟨C,hC,hbound⟩ := spectralWeylContour_normalized_small_bound spectralBesselI H base hFactor
    hCylinder hB hBase hContour hX₀
  refine ⟨C,hC,?_⟩
  intro R X hR hX hXX
  have hint := spectralWeylContour_integrable_line spectralBesselI H base hFactor hCylinder hB hBase
    hR hX (hContour R X hR hX) (y:=0) (by norm_num) (by norm_num)
  simp only [Complex.ofReal_zero,zero_mul,add_zero] at hint
  rw [(spectralWeylKGaussian_eq_contour H hEven R hX hint).2]
  exact hbound R X hR hX hXX

theorem spectralABLRegular_JKGaussian_small_bound (T Δ : ℝ) (hT : 0 < T) (hΔ : 0 < Δ)
    {X₀ : ℝ} (hX₀ : 0 < X₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ R X : ℝ, 1 ≤ R → 0 < X → X ≤ X₀ →
      ‖∫ t : ℝ, spectralWeylJMultiplier t X*spectralABLRegularCorrected T Δ (t : ℂ)*
        Complex.exp (-2*((t : ℂ)/(R : ℂ))^2) ∂spectralKLSpectralMeasure‖ ≤ C*X^(1/4 : ℝ) ∧
      ‖∫ t : ℝ, spectralWeylKMultiplier t X*spectralABLRegularCorrected T Δ (t : ℂ)*
        Complex.exp (-2*((t : ℂ)/(R : ℂ))^2) ∂spectralKLSpectralMeasure‖ ≤ C*X^(1/4 : ℝ) := by
  obtain ⟨B,hB,hBase⟩ := spectralABLRegularBase_strip_decay_two T Δ hT hΔ
  have hb (t y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 5/8) :=
    hBase t y (by rw [abs_of_nonneg hy0]; linarith)
  have hh (z : ℂ) (hz0 : 0 ≤ z.im) (hz1 : z.im ≤ 5/8) :=
    spectralABLRegularCorrected_differentiableAt T Δ z (by rw [abs_of_nonneg hz0]; linarith)
  obtain ⟨Cj,hCj,hJ⟩ := spectralWeylJGaussian_small_of_base
    (spectralABLRegularCorrected T Δ) (spectralABLRegularBase T Δ)
    (spectralABLRegularCorrected_even T Δ) (fun _ => rfl) hh hB hb hX₀
  obtain ⟨Ck,hCk,hK⟩ := spectralWeylKGaussian_small_of_base
    (spectralABLRegularCorrected T Δ) (spectralABLRegularBase T Δ)
    (spectralABLRegularCorrected_even T Δ) (fun _ => rfl) hh hB hb hX₀
  refine ⟨Cj+Ck,by positivity,?_⟩
  intro R X hR hX hXX
  constructor
  · exact (hJ R X hR hX hXX).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCk.le) (Real.rpow_nonneg hX.le _))
  · exact (hK R X hR hX hXX).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCj.le) (Real.rpow_nonneg hX.le _))

theorem spectralABLExceptional_JKGaussian_small_bound (a : ℝ) {A : ℕ} (hA : 2 ≤ A)
    {X₀ : ℝ} (hX₀ : 0 < X₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ R X : ℝ, 1 ≤ R → 0 < X → X ≤ X₀ →
      ‖∫ t : ℝ, spectralWeylJMultiplier t X*spectralABLExceptionalCorrected a A (t : ℂ)*
        Complex.exp (-2*((t : ℂ)/(R : ℂ))^2) ∂spectralKLSpectralMeasure‖ ≤ C*X^(1/4 : ℝ) ∧
      ‖∫ t : ℝ, spectralWeylKMultiplier t X*spectralABLExceptionalCorrected a A (t : ℂ)*
        Complex.exp (-2*((t : ℂ)/(R : ℂ))^2) ∂spectralKLSpectralMeasure‖ ≤ C*X^(1/4 : ℝ) := by
  obtain ⟨B,hB,hBase⟩ := spectralABLExceptionalBase_strip_decay_two a hA
  have hb (t y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 5/8) :=
    hBase t y (by rw [abs_of_nonneg hy0]; linarith)
  have hh (z : ℂ) (hz0 : 0 ≤ z.im) (hz1 : z.im ≤ 5/8) :=
    spectralABLExceptionalCorrected_differentiableAt a (by omega : 1 ≤ A) z
      (by rw [abs_of_nonneg hz0]; linarith)
  obtain ⟨Cj,hCj,hJ⟩ := spectralWeylJGaussian_small_of_base
    (spectralABLExceptionalCorrected a A) (spectralABLExceptionalBase a A)
    (spectralABLExceptionalCorrected_even a A) (fun _ => rfl) hh hB hb hX₀
  obtain ⟨Ck,hCk,hK⟩ := spectralWeylKGaussian_small_of_base
    (spectralABLExceptionalCorrected a A) (spectralABLExceptionalBase a A)
    (spectralABLExceptionalCorrected_even a A) (fun _ => rfl) hh hB hb hX₀
  refine ⟨Cj+Ck,by positivity,?_⟩
  intro R X hR hX hXX
  constructor
  · exact (hJ R X hR hX hXX).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCk.le) (Real.rpow_nonneg hX.le _))
  · exact (hK R X hR hX hXX).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCj.le) (Real.rpow_nonneg hX.le _))

end
end ArtinMatthews
