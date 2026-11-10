module

public import ArtinMatthews.SpectralBesselOrderBound
public import ArtinMatthews.SpectralBesselOrderAnalytic
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform positive-argument bounds for the genuine complex-order
derivative. The constants are explicit convergent logarithmic integrals. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace ArtinMatthews

theorem spectralKLogKernel_norm_antitone (ν : ℂ) (a x u : ℝ) (hax : a ≤ x) :
    ‖spectralKLogKernel ν x u‖ ≤ ‖spectralKLogKernel ν a u‖ := by
  simp only [spectralKLogKernel,Complex.norm_exp,Complex.add_re,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  apply Real.exp_le_exp.mpr
  have hc := Real.cosh_pos u
  nlinarith

theorem spectralKOrderDerivativeKernel_integrable (ν : ℂ) {x : ℝ} (hx : 0 < x) :
    Integrable (spectralKOrderDerivativeKernel ν x) := by
  apply (spectralKOrderDerivativeKernel_majorant_integrable ν hx).mono'
    (spectralKOrderDerivativeKernel_continuous ν x).aestronglyMeasurable
  exact ae_of_all _ (fun u => spectralKOrderDerivativeKernel_bound ν ν x u (by simp))

def spectralKOrderUniformBound (ν : ℂ) (a : ℝ) : ℝ :=
  (1/2 : ℝ)*∫ u : ℝ, ‖spectralKLogKernel (ν+2) a u‖+‖spectralKLogKernel (ν-2) a u‖

theorem spectralKOrderUniformBound_nonneg (ν : ℂ) (a : ℝ) :
    0 ≤ spectralKOrderUniformBound ν a :=
  mul_nonneg (by norm_num) (integral_nonneg (fun _ => add_nonneg (norm_nonneg _) (norm_nonneg _)))

theorem schlafliBesselK_order_deriv_uniform (ν ν₀ : ℂ) (a x : ℝ)
    (ha : 0 < a) (hax : a ≤ x) (hν : ν ∈ Metric.ball ν₀ 1) :
    ‖deriv (fun μ => OAI.CubicEisenstein.schlafliBesselK μ x) ν‖ ≤
      spectralKOrderUniformBound ν₀ a := by
  have hx : 0 < x := ha.trans_le hax
  rw [(schlafliBesselK_order_hasDerivAt ν hx).deriv,norm_mul]
  have hc : ‖(1/2 : ℂ)‖ = (1/2 : ℝ) := by norm_num
  rw [hc]
  change (1/2 : ℝ)*‖∫ u : ℝ,spectralKOrderDerivativeKernel ν x u‖ ≤
    (1/2 : ℝ)*∫ u : ℝ,‖spectralKLogKernel (ν₀+2) a u‖+‖spectralKLogKernel (ν₀-2) a u‖
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    _ ≤ ∫ u : ℝ, ‖spectralKOrderDerivativeKernel ν x u‖ := norm_integral_le_integral_norm _
    _ ≤ _ := integral_mono (spectralKOrderDerivativeKernel_integrable ν hx).norm
      (spectralKOrderDerivativeKernel_majorant_integrable ν₀ ha) (fun u =>
        (spectralKOrderDerivativeKernel_ball_bound ν ν₀ x u hν).trans
          (add_le_add (spectralKLogKernel_norm_antitone (ν₀+2) a x u hax)
            (spectralKLogKernel_norm_antitone (ν₀-2) a x u hax)))

end ArtinMatthews
