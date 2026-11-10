module

public import OAI.NumberTheory.DirichletL.Eisenstein.HyperbolicSpace
public import ArtinMatthews.SpectralBesselOrderAnalytic
public import ArtinMatthews.SpectralKOrderDominance
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set Metric OAI.CubicEisenstein
noncomputable section

theorem schlafliBesselK_order_deriv_half_strip {ν : ℂ} (hν : |ν.re| ≤ 9 / 16)
    {x : ℝ} (hx : 0 < x) :
    ‖deriv (fun μ : ℂ => schlafliBesselK μ x) ν‖ ≤
      32 * ‖schlafliBesselK (5 / 8 : ℂ) x‖ := by
  have hd : DiffContOnCl ℂ (fun μ : ℂ => schlafliBesselK μ x) (Metric.ball ν (1 / 32)) :=
    (schlafliBesselK_order_differentiable hx).diffContOnCl
  apply (Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (C := ‖schlafliBesselK (5 / 8 : ℂ) x‖) (by norm_num : (0 : ℝ) < 1 / 32) hd ?_).trans_eq (by ring)
  intro μ hμ
  have hdist : ‖μ - ν‖ = (1 / 32 : ℝ) := by simpa only [Metric.mem_sphere, dist_eq_norm] using hμ
  have hre : |μ.re| ≤ (5 / 8 : ℝ) := by
    have hr := Complex.abs_re_le_norm (μ - ν)
    have ha := abs_add_le ν.re (μ - ν).re
    rw [show ν.re + (μ - ν).re = μ.re by simp] at ha
    linarith
  simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using
    schlafliBesselK_order_norm_le (5 / 8) (by norm_num) hre hx

end
end ArtinMatthews
