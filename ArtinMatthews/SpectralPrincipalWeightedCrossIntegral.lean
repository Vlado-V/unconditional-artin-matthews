module

public import ArtinMatthews.SpectralPrincipalWeightedMeasure
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import ArtinMatthews.SpectralPrincipalWeightedDensity
public import Mathlib.MeasureTheory.Function.L2Space


set_option backward.privateInPublic true
@[expose] public section

/-! Weighted Cauchy--Schwarz for measurable principal spectral densities,
with absolute integrability of the genuine cross term. -/
namespace ArtinMatthews
open Set MeasureTheory Filter
noncomputable section

private theorem integral_norm_le_sqrt_densities
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (F G : α → ℝ) (h : α → ℂ)
    (hF : ∀ x, 0 ≤ F x) (hG : ∀ x, 0 ≤ G x)
    (hFi : Integrable F μ) (hGi : Integrable G μ) (hh : AEMeasurable h μ)
    {H : ℝ} (hH : 0 ≤ H)
    (hbound : ∀ᵐ x ∂μ, ‖h x‖ ≤ H*(Real.sqrt (F x)*Real.sqrt (G x))) :
    Integrable h μ ∧
      (∫ x, ‖h x‖ ∂μ) ≤ H*Real.sqrt (∫ x, F x ∂μ)*Real.sqrt (∫ x, G x ∂μ) := by
  let a (x : α) := Real.sqrt (F x)
  let b (x : α) := Real.sqrt (G x)
  have ham : AEStronglyMeasurable a μ := hFi.aestronglyMeasurable.aemeasurable.sqrt.aestronglyMeasurable
  have hbm : AEStronglyMeasurable b μ := hGi.aestronglyMeasurable.aemeasurable.sqrt.aestronglyMeasurable
  have ha : MemLp a 2 μ := (memLp_two_iff_integrable_sq ham).mpr
    (hFi.congr (Eventually.of_forall fun x => (Real.sq_sqrt (hF x)).symm))
  have hb : MemLp b 2 μ := (memLp_two_iff_integrable_sq hbm).mpr
    (hGi.congr (Eventually.of_forall fun x => (Real.sq_sqrt (hG x)).symm))
  have hab : Integrable (fun x => a x*b x) μ := ha.integrable_mul hb
  have hmajor : Integrable (fun x => H*(a x*b x)) μ := hab.const_mul H
  have hi : Integrable h μ := hmajor.mono' hh.aestronglyMeasurable hbound
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Eventually.of_forall fun x => Real.sqrt_nonneg (F x))
    (Eventually.of_forall fun x => Real.sqrt_nonneg (G x))
    (show MemLp a (ENNReal.ofReal (2 : ℝ)) μ by simpa using ha)
    (show MemLp b (ENNReal.ofReal (2 : ℝ)) μ by simpa using hb)
  have hia : (∫ x, (a x)^(2 : ℝ) ∂μ) = ∫ x, F x ∂μ := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change (a x)^(2 : ℝ) = F x
      rw [Real.rpow_two]
      exact Real.sq_sqrt (hF x)
  have hib : (∫ x, (b x)^(2 : ℝ) ∂μ) = ∫ x, G x ∂μ := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change (b x)^(2 : ℝ) = G x
      rw [Real.rpow_two]
      exact Real.sq_sqrt (hG x)
  rw [hia,hib,← Real.sqrt_eq_rpow,← Real.sqrt_eq_rpow] at hcs
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ x, H*(a x*b x) ∂μ := integral_mono_ae hi.norm hmajor hbound
    _ = H*(∫ x, a x*b x ∂μ) := integral_const_mul _ _
    _ ≤ H*(Real.sqrt (∫ x, F x ∂μ)*Real.sqrt (∫ x, G x ∂μ)) :=
      mul_le_mul_of_nonneg_left hcs hH
    _ = _ := by ring

theorem spectralPrincipal_cross_integral
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (τ f g : α → ℝ) (h : α → ℂ)
    (hτ : Measurable τ) (hfm : AEMeasurable f μ) (hgm : AEMeasurable g μ)
    (hh : AEMeasurable h μ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    {H Z B₁ B₂ C₁ C₂ : ℝ} (hH : 0 ≤ H) (hZ : 1 ≤ Z)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hbound : ∀ᵐ x ∂μ, ‖h x‖ ≤
      H*spectralPrincipalDecayWeight Z (τ x)*Real.sqrt (f x)*Real.sqrt (g x))
    (hcut₁ : ∀ R : ℝ, 1 ≤ R →
      IntegrableOn f (spectralPrincipalCutoff τ R) μ ∧
        (∫ x in spectralPrincipalCutoff τ R, f x ∂μ) ≤ C₁*(R^2+B₁*R))
    (hcut₂ : ∀ R : ℝ, 1 ≤ R →
      IntegrableOn g (spectralPrincipalCutoff τ R) μ ∧
        (∫ x in spectralPrincipalCutoff τ R, g x ∂μ) ≤ C₂*(R^2+B₂*R)) :
    Integrable h μ ∧
      (∫ x, ‖h x‖ ∂μ) ≤
        H*Real.sqrt (8*C₁*(Z^2+B₁*Z))*Real.sqrt (8*C₂*(Z^2+B₂*Z)) := by
  have h₁ := spectralPrincipal_weighted_density μ τ f hτ hfm hf hB₁ hC₁ hZ hcut₁
  have h₂ := spectralPrincipal_weighted_density μ τ g hτ hgm hg hB₂ hC₂ hZ hcut₂
  let F (x : α) := f x*spectralPrincipalDecayWeight Z (τ x)
  let G (x : α) := g x*spectralPrincipalDecayWeight Z (τ x)
  have hF (x : α) : 0 ≤ F x := mul_nonneg (hf x) (spectralPrincipalDecayWeight_nonneg Z (τ x))
  have hG (x : α) : 0 ≤ G x := mul_nonneg (hg x) (spectralPrincipalDecayWeight_nonneg Z (τ x))
  have hdom : ∀ᵐ x ∂μ, ‖h x‖ ≤ H*(Real.sqrt (F x)*Real.sqrt (G x)) := by
    filter_upwards [hbound] with x hx
    have he : Real.sqrt (F x)*Real.sqrt (G x) =
        spectralPrincipalDecayWeight Z (τ x)*Real.sqrt (f x)*Real.sqrt (g x) := by
      dsimp [F,G]
      rw [Real.sqrt_mul (hf x), Real.sqrt_mul (hg x)]
      calc
        _ = (Real.sqrt (f x)*Real.sqrt (g x))*
            (Real.sqrt (spectralPrincipalDecayWeight Z (τ x)))^2 := by ring
        _ = _ := by rw [Real.sq_sqrt (spectralPrincipalDecayWeight_nonneg Z (τ x))]; ring
    rw [he]
    simpa only [mul_assoc] using hx
  obtain ⟨hi,hni⟩ := integral_norm_le_sqrt_densities μ F G h hF hG h₁.1 h₂.1 hh hH hdom
  refine ⟨hi,hni.trans ?_⟩
  have hleft := Real.sqrt_le_sqrt h₁.2
  have hright := Real.sqrt_le_sqrt h₂.2
  exact mul_le_mul (mul_le_mul_of_nonneg_left hleft hH) hright
    (Real.sqrt_nonneg _) (mul_nonneg hH (Real.sqrt_nonneg _))

end
end ArtinMatthews
