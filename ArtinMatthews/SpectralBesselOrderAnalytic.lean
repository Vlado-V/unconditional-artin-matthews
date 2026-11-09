module

public import ArtinMatthews.SpectralBesselOrderBound
public import Mathlib.Analysis.Complex.CauchyIntegral


set_option backward.privateInPublic true
@[expose] public section

/-! Entire order dependence of the actual Schlaefli K function, proved by
complex differentiation of its absolutely convergent logarithmic integral. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace ArtinMatthews

theorem spectralKLogKernel_order_hasDerivAt (ν : ℂ) (x u : ℝ) :
    HasDerivAt (fun μ => spectralKLogKernel μ x u) (spectralKOrderDerivativeKernel ν x u) ν := by
  have h := ((hasDerivAt_id ν).mul_const (u : ℂ)).const_add
    (((-(x*Real.cosh u) : ℝ) : ℂ))
  simpa only [spectralKLogKernel,spectralKOrderDerivativeKernel,Function.comp_def,id_eq,one_mul,mul_one,mul_comm] using
    (Complex.hasDerivAt_exp _).comp ν h

theorem spectralKLogKernel_continuous (ν : ℂ) (x : ℝ) :
    Continuous (spectralKLogKernel ν x) := by
  unfold spectralKLogKernel
  fun_prop

theorem spectralKOrderDerivativeKernel_continuous (ν : ℂ) (x : ℝ) :
    Continuous (spectralKOrderDerivativeKernel ν x) := by
  unfold spectralKOrderDerivativeKernel
  exact Complex.continuous_ofReal.mul (spectralKLogKernel_continuous ν x)

theorem spectralKOrderDerivativeKernel_ball_bound (ν ν₀ : ℂ) (x u : ℝ)
    (hν : ν ∈ Metric.ball ν₀ 1) :
    ‖spectralKOrderDerivativeKernel ν x u‖ ≤
      ‖spectralKLogKernel (ν₀+2) x u‖+‖spectralKLogKernel (ν₀-2) x u‖ := by
  have hd : ‖ν-ν₀‖ < 1 := by simpa only [Metric.mem_ball,dist_eq_norm] using hν
  have hr : |ν.re-ν₀.re| ≤ ‖ν-ν₀‖ := by
    simpa only [Complex.sub_re] using Complex.abs_re_le_norm (ν-ν₀)
  exact spectralKOrderDerivativeKernel_bound ν ν₀ x u (hr.trans hd.le)

theorem spectralKLogIntegral_order_hasDerivAt (ν : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun μ => ∫ u : ℝ, spectralKLogKernel μ x u)
      (∫ u : ℝ, spectralKOrderDerivativeKernel ν x u) ν := by
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun μ u => spectralKLogKernel μ x u)
    (F' := fun μ u => spectralKOrderDerivativeKernel μ x u)
    (μ := volume) (s := Metric.ball ν 1)
    (Metric.ball_mem_nhds ν (by norm_num : (0 : ℝ) < 1))
    (Filter.Eventually.of_forall fun μ => (spectralKLogKernel_continuous μ x).aestronglyMeasurable)
    (spectralKLogKernel_integrable ν hx)
    (spectralKOrderDerivativeKernel_continuous ν x).aestronglyMeasurable
    (ae_of_all _ fun u μ hμ => spectralKOrderDerivativeKernel_ball_bound μ ν x u hμ)
    (spectralKOrderDerivativeKernel_majorant_integrable ν hx)
    (ae_of_all _ fun u μ _ => spectralKLogKernel_order_hasDerivAt μ x u)
  exact h.2

theorem schlafliBesselK_order_hasDerivAt (ν : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun μ => OAI.CubicEisenstein.schlafliBesselK μ x)
      ((1/2 : ℂ)*∫ u : ℝ, spectralKOrderDerivativeKernel ν x u) ν := by
  have he : (fun μ => OAI.CubicEisenstein.schlafliBesselK μ x) =
      fun μ => (1/2 : ℂ)*∫ u : ℝ, spectralKLogKernel μ x u := by
    funext μ
    exact schlafliBesselK_hyperbolic_integral μ hx
  rw [he]
  exact (spectralKLogIntegral_order_hasDerivAt ν hx).const_mul (1/2 : ℂ)

theorem schlafliBesselK_order_differentiable {x : ℝ} (hx : 0 < x) :
    Differentiable ℂ (fun μ => OAI.CubicEisenstein.schlafliBesselK μ x) :=
  fun μ => (schlafliBesselK_order_hasDerivAt μ hx).differentiableAt

theorem schlafliBesselK_order_analytic {x : ℝ} (hx : 0 < x) :
    AnalyticOnNhd ℂ (fun μ => OAI.CubicEisenstein.schlafliBesselK μ x) univ :=
  fun μ _ => (schlafliBesselK_order_differentiable hx).analyticAt μ

end ArtinMatthews
