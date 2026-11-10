module

public import ArtinMatthews.SpectralKLCompactOrder
public import ArtinMatthews.SpectralBesselKEquation
public import ArtinMatthews.SpectralBesselOrderAnalytic
public import ArtinMatthews.SpectralKLPowerAnalysis
public import ArtinMatthews.SpectralKOrderDerivativeEnvelope
public import ArtinMatthews.SpectralKOrderDominance
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Presheaf


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory Filter OAI.CubicEisenstein
open scoped Topology
noncomputable section

theorem spectralKLPowerOrderDerivative_measurable (f : ℝ → ℂ) (hf : Measurable f) (ν : ℂ) :
    StronglyMeasurable (spectralKLCompactOrderDerivativeIntegrand f ν) := by
  have hk : Continuous (fun p : ℝ × ℝ => spectralKOrderDerivativeKernel ν p.1 p.2) := by
    unfold spectralKOrderDerivativeKernel spectralKLogKernel
    fun_prop
  exact (stronglyMeasurable_const.mul hk.stronglyMeasurable.integral_prod_right').mul
    (hf.div Complex.continuous_ofReal.measurable).stronglyMeasurable

theorem spectralKLPowerOrderIntegrand_measurable (f : ℝ → ℂ) (hf : Measurable f)
    (hfzero : ∀ x : ℝ, x ≤ 0 → f x = 0) (ν : ℂ) :
    AEStronglyMeasurable (spectralKLCompactOrderIntegrand f ν) := by
  have hk : ContinuousOn (schlafliBesselK ν) (Ioi (0 : ℝ)) := by
    intro x hx
    exact (schlafliBesselK_hasDerivAt ν x hx).continuousAt.continuousWithinAt
  have hm := hk.measurable_piecewise (f := schlafliBesselK ν) (g := fun _ => (0 : ℂ))
    continuousOn_const measurableSet_Ioi
  have hprod := hm.mul (hf.div Complex.continuous_ofReal.measurable)
  apply hprod.aestronglyMeasurable.congr
  filter_upwards with x
  by_cases hx : 0 < x
  · simp [spectralKLCompactOrderIntegrand, spectralKLPhysicalCompactDiv, Set.piecewise, hx]
  · simp [spectralKLCompactOrderIntegrand, spectralKLPhysicalCompactDiv, Set.piecewise, hx,
      hfzero x (le_of_not_gt hx)]

theorem spectralKLPowerOrderTransform_hasDerivAt (f : ℝ → ℂ) (hf : Measurable f)
    (hfzero : ∀ x : ℝ, x ≤ 0 → f x = 0) (M : ℝ) (hM : 0 ≤ M)
    (hpower : ∀ x : ℝ, 0 < x → ‖f x‖ ≤ M * x ^ (3 / 4 : ℝ))
    (ν : ℂ) (hν : |ν.re| ≤ 1 / 2) :
    HasDerivAt (spectralKLCompactOrderTransform f)
      (∫ x : ℝ, spectralKLCompactOrderDerivativeIntegrand f ν x) ν := by
  let D : ℝ → ℝ := (Ioi (0 : ℝ)).indicator
    (fun x : ℝ => 32 * M * (x ^ (3 / 4 - 1 : ℝ) * ‖schlafliBesselK (5 / 8 : ℂ) x‖))
  have hD : Integrable D := by
    have hDi : IntegrableOn (fun x : ℝ => 32 * M *
        (x ^ (3 / 4 - 1 : ℝ) * ‖schlafliBesselK (5 / 8 : ℂ) x‖)) (Ioi (0 : ℝ)) := by
      convert (spectralK_power_integrable (5 / 8) (3 / 4) (by norm_num)).const_mul (32 * M) using 1
      simp only [IntegrableOn, Complex.ofReal_div, Complex.ofReal_ofNat]
    exact hDi.integrable_indicator measurableSet_Ioi
  have hμ (μ : ℂ) (hh : μ ∈ Metric.ball ν (1 / 32)) : |μ.re| ≤ 9 / 16 := by
    have hn : ‖μ - ν‖ < (1 / 32 : ℝ) := by simpa only [Metric.mem_ball, dist_eq_norm] using hh
    have hr := Complex.abs_re_le_norm (μ - ν)
    have ha := abs_add_le ν.re (μ - ν).re
    rw [show ν.re + (μ - ν).re = μ.re by simp] at ha
    linarith
  have hbound (μ : ℂ) (hball : μ ∈ Metric.ball ν (1 / 32)) (x : ℝ) :
      ‖spectralKLCompactOrderDerivativeIntegrand f μ x‖ ≤ D x := by
    by_cases hx : 0 < x
    · have hk := schlafliBesselK_order_deriv_half_strip (hμ μ hball) hx
      rw [spectralKLCompactOrderDerivativeIntegrand, norm_mul,
        ← (schlafliBesselK_order_hasDerivAt μ hx).deriv,
        spectralKLPhysicalCompactDiv, norm_div, Complex.norm_real, Real.norm_of_nonneg hx.le]
      dsimp only [D]
      rw [Set.indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx)]
      calc
        _ ≤ (32 * ‖schlafliBesselK (5 / 8 : ℂ) x‖) * ((M * x ^ (3 / 4 : ℝ)) / x) := by gcongr; exact hpower x hx
        _ = _ := by rw [Real.rpow_sub hx, Real.rpow_one]; ring
    · have hxmem : x ∉ Ioi (0 : ℝ) := hx
      simp only [spectralKLCompactOrderDerivativeIntegrand, spectralKLPhysicalCompactDiv,
        hfzero x (le_of_not_gt hx), zero_div, mul_zero, norm_zero, D,
        Set.indicator_of_notMem hxmem, le_refl]
  have hi : Integrable (spectralKLCompactOrderIntegrand f ν) := by
    have hi := spectralKLPower_analysis_integrable f hf M (3 / 4) (5 / 8) hM (by norm_num)
      (by norm_num) hpower ν (hν.trans (by norm_num))
    apply hi.integrable_of_forall_notMem_eq_zero
    intro x hx
    simp [hfzero x (le_of_not_gt hx)]
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun μ x => spectralKLCompactOrderIntegrand f μ x)
    (F' := fun μ x => spectralKLCompactOrderDerivativeIntegrand f μ x)
    (μ := volume) (s := Metric.ball ν (1 / 32)) (Metric.ball_mem_nhds ν (by norm_num))
    (Eventually.of_forall (spectralKLPowerOrderIntegrand_measurable f hf hfzero)) hi
    (spectralKLPowerOrderDerivative_measurable f hf ν).aestronglyMeasurable
    (ae_of_all _ fun x μ hball => hbound μ hball x) hD ?_).2
  filter_upwards with x
  intro μ _
  by_cases hx : 0 < x
  · exact (schlafliBesselK_order_hasDerivAt μ hx).mul_const _
  · simpa only [spectralKLCompactOrderIntegrand, spectralKLCompactOrderDerivativeIntegrand,
      spectralKLPhysicalCompactDiv, hfzero x (le_of_not_gt hx), zero_div, mul_zero]
      using hasDerivAt_const μ (0 : ℂ)

end
end ArtinMatthews
