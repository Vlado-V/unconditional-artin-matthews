module

public import ArtinMatthews.SpectralCuspBesselOrderIntegrand


set_option backward.privateInPublic true
@[expose] public section

/-! Entire order dependence of the actual compact-height K transform.
The order derivative is an absolutely integrable literal height integral. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace ArtinMatthews

theorem cuspBesselTransform_order_hasDerivAt (ν : ℂ) {q Y : ℝ}
    (hq : 0 < q) (hY : 0 < Y) (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hcρ : HasCompactSupport ρ) (hsρ : tsupport ρ ⊆ Ioi Y) :
    IntegrableOn (cuspBesselOrderDerivativeIntegrand ν q ρ) (Ioi Y) ∧
      HasDerivAt (fun μ => cuspBesselTransform μ q Y ρ)
        (∫ y in Ioi Y,cuspBesselOrderDerivativeIntegrand ν q ρ y) ν := by
  have hpρ : tsupport ρ ⊆ Ioi (0 : ℝ) := fun y hy => hY.trans (hsρ hy)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun μ y => cuspBesselTransformIntegrand μ q ρ y)
    (F' := fun μ y => cuspBesselOrderDerivativeIntegrand μ q ρ y)
    (μ := volume.restrict (Ioi Y)) (s := Metric.ball ν 1)
    (Metric.ball_mem_nhds ν (by norm_num : (0 : ℝ) < 1))
    (Filter.Eventually.of_forall fun μ =>
      (cuspBesselTransformIntegrand_continuous μ hq hY ρ hρ.continuous hsρ).aestronglyMeasurable)
    (cuspBesselTransformIntegrand_integrable ν hq hY ρ hρ.continuous hcρ hsρ).restrict
    (cuspBesselOrderDerivativeIntegrand_stronglyMeasurable ν q ρ hρ hpρ).aestronglyMeasurable
    (ae_of_all _ fun y μ hμ => cuspBesselOrderDerivativeIntegrand_bound μ ν hq hY ρ hsρ hμ y)
    (cuspBesselOrderDerivative_majorant_integrable ν q Y ρ hρ hcρ hpρ).restrict
    (ae_of_all _ fun y μ _ => cuspBesselTransformIntegrand_order_hasDerivAt μ hq hY ρ hsρ y)
  exact h

theorem cuspBesselTransform_order_differentiable {q Y : ℝ}
    (hq : 0 < q) (hY : 0 < Y) (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hcρ : HasCompactSupport ρ) (hsρ : tsupport ρ ⊆ Ioi Y) :
    Differentiable ℂ (fun μ => cuspBesselTransform μ q Y ρ) :=
  fun μ => (cuspBesselTransform_order_hasDerivAt μ hq hY ρ hρ hcρ hsρ).2.differentiableAt

theorem cuspBesselTransform_order_analytic {q Y : ℝ}
    (hq : 0 < q) (hY : 0 < Y) (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hcρ : HasCompactSupport ρ) (hsρ : tsupport ρ ⊆ Ioi Y) :
    AnalyticOnNhd ℂ (fun μ => cuspBesselTransform μ q Y ρ) univ :=
  fun μ _ => (cuspBesselTransform_order_differentiable hq hY ρ hρ hcρ hsρ).analyticAt μ

theorem cuspBesselTransform_shifted_order_analytic {q Y : ℝ}
    (hq : 0 < q) (hY : 0 < Y) (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hcρ : HasCompactSupport ρ) (hsρ : tsupport ρ ⊆ Ioi Y) :
    AnalyticOnNhd ℂ (fun s => cuspBesselTransform (s-1/2) q Y ρ) univ := by
  have hd := (cuspBesselTransform_order_differentiable hq hY ρ hρ hcρ hsρ).comp
    (differentiable_id.sub (differentiable_const (1/2 : ℂ)))
  exact fun s _ => hd.analyticAt s

end ArtinMatthews
