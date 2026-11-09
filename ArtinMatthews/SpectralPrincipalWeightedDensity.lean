module

public import ArtinMatthews.SpectralPrincipalWeightedMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap


set_option backward.privateInPublic true
@[expose] public section

/-! Nonnegative densities with the actual local cutoff integral bounds
inherit the quantitative fourth-power principal spectral estimate. -/
namespace ArtinMatthews
open Set MeasureTheory Filter
noncomputable section

theorem spectralPrincipal_weighted_density
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (τ f : α → ℝ)
    (hτ : Measurable τ) (hfm : AEMeasurable f μ) (hf : ∀ x, 0 ≤ f x)
    {B C Z : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hZ : 1 ≤ Z)
    (hcut : ∀ R : ℝ, 1 ≤ R →
      IntegrableOn f (spectralPrincipalCutoff τ R) μ ∧
        (∫ x in spectralPrincipalCutoff τ R, f x ∂μ) ≤ C*(R^2+B*R)) :
    Integrable (fun x => f x*spectralPrincipalDecayWeight Z (τ x)) μ ∧
      (∫ x, f x*spectralPrincipalDecayWeight Z (τ x) ∂μ) ≤ 8*C*(Z^2+B*Z) := by
  let ν := μ.withDensity (fun x => ENNReal.ofReal (f x))
  have hmass (R : ℝ) (hR : 1 ≤ R) :
      ν (spectralPrincipalCutoff τ R) ≤ ENNReal.ofReal (C*(R^2+B*R)) := by
    change μ.withDensity (fun x => ENNReal.ofReal (f x)) (spectralPrincipalCutoff τ R) ≤ _
    rw [withDensity_apply _ (spectralPrincipalCutoff_measurable hτ R)]
    rw [← ofReal_integral_eq_lintegral_ofReal (hcut R hR).1 (Eventually.of_forall hf)]
    exact ENNReal.ofReal_le_ofReal (hcut R hR).2
  have h := spectralPrincipalDecayWeight_integrable_bound ν τ hτ hB hC hZ hmass
  have hm : AEMeasurable (fun x => ENNReal.ofReal (f x)) μ := hfm.ennreal_ofReal
  have ht : ∀ᵐ x ∂μ, ENNReal.ofReal (f x) < ⊤ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have he :
      (fun x => (ENNReal.ofReal (f x)).toReal • spectralPrincipalDecayWeight Z (τ x)) =
      fun x => f x*spectralPrincipalDecayWeight Z (τ x) := by
    funext x
    rw [ENNReal.toReal_ofReal (hf x), smul_eq_mul]
  have hi := (integrable_withDensity_iff_integrable_smul₀' hm ht).mp h.1
  refine ⟨by simpa only [he] using hi, ?_⟩
  have hv := integral_withDensity_eq_integral_toReal_smul₀ hm ht
    (fun x => spectralPrincipalDecayWeight Z (τ x))
  change (∫ x, spectralPrincipalDecayWeight Z (τ x) ∂ν) =
    (∫ x, (ENNReal.ofReal (f x)).toReal • spectralPrincipalDecayWeight Z (τ x) ∂μ) at hv
  rw [he] at hv
  exact hv.symm.trans_le h.2

end
end ArtinMatthews
