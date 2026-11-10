module

public import ArtinMatthews.SpectralKLWeightedMeasures
public import ArtinMatthews.SpectralWeylMultipliers
public import ArtinMatthews.SpectralWeylSpectralContinuity
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
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual continuous J synthesis for a spectrally weighted integrable
coefficient. The order bound gives absolute convergence at each positive
modulus and locally uniform domination in that modulus. -/
namespace ArtinMatthews
open Set MeasureTheory Filter
open scoped Topology

noncomputable section

def spectralJWeightedSynthesis (H : ℝ → ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) / 2 * ∫ r : ℝ, spectralWeylJMultiplier r x * H r ∂spectralKLSpectralMeasure

private def spectralJWeightedScaledIntegrand (H : ℝ → ℂ) (x r : ℝ) : ℂ :=
  ((x : ℂ) * spectralWeylJMultiplier r x) * H r

private theorem spectralJWeightedScaledIntegrand_aestronglyMeasurable
    (H : ℝ → ℂ) (hH : AEMeasurable H spectralKLSpectralMeasure) (x : ℝ) :
    AEStronglyMeasurable (spectralJWeightedScaledIntegrand H x) spectralKLSpectralMeasure := by
  have hM : Measurable (fun r : ℝ => spectralWeylJMultiplier r x) :=
    spectralWeylJMultiplier_measurable.comp (measurable_id.prodMk measurable_const)
  exact ((measurable_const.mul hM).aemeasurable.mul hH).aestronglyMeasurable

private theorem spectralJWeightedScaledIntegrand_norm_le
    (H : ℝ → ℂ) {x r : ℝ} (hx : 0 < x) (hr : 0 < r) :
    ‖spectralJWeightedScaledIntegrand H x r‖ ≤
      (4 * Real.pi * Real.exp (x^2/4)) *
        (‖H r‖ * (1 + (Real.sqrt (Real.cosh Real.pi) / Real.pi) / r)) := by
  rw [spectralJWeightedScaledIntegrand, norm_mul]
  calc
    _ ≤ (4 * Real.pi * Real.exp (x^2/4) *
        (1 + (Real.sqrt (Real.cosh Real.pi) / Real.pi) / r)) * ‖H r‖ :=
      mul_le_mul_of_nonneg_right (spectralWeylJMultiplier_order_bound hr hx) (norm_nonneg _)
    _ = _ := by ring

theorem spectralJWeightedSynthesis_integrand_integrable (H : ℝ → ℂ)
    (hH : AEMeasurable H spectralKLSpectralMeasure)
    (hW : Integrable (fun r : ℝ =>
      ‖H r‖ * (1 + (Real.sqrt (Real.cosh Real.pi) / Real.pi) / r)) spectralKLSpectralMeasure)
    {x : ℝ} (hx : 0 < x) :
    Integrable (fun r : ℝ => spectralWeylJMultiplier r x * H r) spectralKLSpectralMeasure := by
  have hi : Integrable (spectralJWeightedScaledIntegrand H x) spectralKLSpectralMeasure := by
    apply (hW.const_mul (4*Real.pi*Real.exp (x^2/4))).mono'
      (spectralJWeightedScaledIntegrand_aestronglyMeasurable H hH x)
    filter_upwards [spectralKLPositiveWeightMeasure_ae_pos spectralKLPlancherelWeight] with r hr
    exact spectralJWeightedScaledIntegrand_norm_le H hx hr
  apply (hi.const_mul (x : ℂ)⁻¹).congr
  filter_upwards with r
  unfold spectralJWeightedScaledIntegrand
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hxC, one_mul]

private theorem spectralJWeightedSynthesis_eq_scaled (H : ℝ → ℂ) (x : ℝ) :
    spectralJWeightedSynthesis H x =
      (1/2 : ℂ) * ∫ r : ℝ, spectralJWeightedScaledIntegrand H x r ∂spectralKLSpectralMeasure := by
  have hi :
      (∫ r : ℝ, spectralJWeightedScaledIntegrand H x r ∂spectralKLSpectralMeasure) =
        (x : ℂ) * ∫ r : ℝ, spectralWeylJMultiplier r x * H r ∂spectralKLSpectralMeasure := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with r
    exact mul_assoc _ _ _
  rw [spectralJWeightedSynthesis, hi]
  ring

theorem spectralJWeightedSynthesis_continuousOn (H : ℝ → ℂ)
    (hH : AEMeasurable H spectralKLSpectralMeasure)
    (hW : Integrable (fun r : ℝ =>
      ‖H r‖ * (1 + (Real.sqrt (Real.cosh Real.pi) / Real.pi) / r)) spectralKLSpectralMeasure) :
    ContinuousOn (spectralJWeightedSynthesis H) (Ioi 0) := by
  intro x hx
  change 0 < x at hx
  let B : ℝ := 4*Real.pi*Real.exp ((x+1)^2/4)
  have hi : ContinuousAt (fun y : ℝ =>
      ∫ r : ℝ, spectralJWeightedScaledIntegrand H y r ∂spectralKLSpectralMeasure) x := by
    apply continuousAt_of_dominated
      (bound := fun r : ℝ => B * (‖H r‖ * (1+(Real.sqrt (Real.cosh Real.pi)/Real.pi)/r)))
    · filter_upwards with y
      exact spectralJWeightedScaledIntegrand_aestronglyMeasurable H hH y
    · filter_upwards [Ioo_mem_nhds hx (lt_add_of_pos_right x zero_lt_one)] with y hy
      filter_upwards [spectralKLPositiveWeightMeasure_ae_pos spectralKLPlancherelWeight] with r hr
      have hB : 4*Real.pi*Real.exp (y^2/4) ≤ B := by
        dsimp [B]
        gcongr
        · exact hy.1.le
        · exact hy.2.le
      exact (spectralJWeightedScaledIntegrand_norm_le H hy.1 hr).trans
        (mul_le_mul_of_nonneg_right hB (by positivity))
    · exact hW.const_mul B
    · filter_upwards with r
      have hM := (spectralWeylJMultiplier_continuousOn r x hx).continuousAt (Ioi_mem_nhds hx)
      exact (Complex.continuous_ofReal.continuousAt.mul hM).mul continuousAt_const
  have he : spectralJWeightedSynthesis H = fun y : ℝ =>
      (1/2 : ℂ) * ∫ r : ℝ, spectralJWeightedScaledIntegrand H y r ∂spectralKLSpectralMeasure :=
    funext (spectralJWeightedSynthesis_eq_scaled H)
  rw [he]
  exact (hi.const_mul (1/2 : ℂ)).continuousWithinAt

end
end ArtinMatthews
