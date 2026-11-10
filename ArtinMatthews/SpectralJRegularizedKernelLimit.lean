module

public import ArtinMatthews.SpectralHeatKernelLimit
public import ArtinMatthews.SpectralJRegularizedWeight
public import ArtinMatthews.SpectralJForwardRealSmooth
public import ArtinMatthews.SpectralJForwardRealWeight
public import ArtinMatthews.SpectralJRegularizedIntegrability
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

namespace ArtinMatthews

open Set MeasureTheory Filter
open scoped ContDiff Topology
noncomputable section

theorem spectralJRegularizedWeight_real_tendsto (f : ℝ → ℂ) (t : ℝ) :
    Tendsto (fun L : ℝ => spectralJRegularizedWeight f L (t : ℂ)) atTop
      (𝓝 (spectralJForwardSpectralWeight f (t : ℂ))) := by
  have hq := (Complex.continuous_ofReal.tendsto 1).comp
    (spectralJRegularizationMultiplier_tendsto (l := 1 / 4 + t ^ 2) (by positivity))
  have h := hq.mul_const (spectralJForwardSpectralWeight f (t : ℂ))
  simpa only [spectralJRegularizedWeight_real_eq_factor, Function.comp_def,
    Complex.ofReal_one, one_mul] using h

theorem spectralJRegularizedBareKernel_tendsto (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (m n : ℤ) {X : ℝ} (hX : 0 < X) :
    Tendsto (fun L : ℝ => spectralABLBareKernel (spectralJRegularizedWeight f L) m n X) atTop
      (𝓝 (spectralABLBareKernel (spectralJForwardSpectralWeight f) m n X)) := by
  have hnorm : Integrable (fun t : ℝ => ‖spectralJForwardSpectralWeight f (t : ℂ)‖)
      spectralKLSpectralMeasure := by
    simpa using spectralJForwardSpectralWeight_weighted_integrable f hf hc hp 0 le_rfl
  have hH : Integrable (fun t : ℝ => spectralJForwardSpectralWeight f (t : ℂ))
      spectralKLSpectralMeasure :=
    hnorm.mono' (spectralJForwardSpectralWeight_real_contDiff f hf.continuous hc hp).continuous.aestronglyMeasurable
      (ae_of_all _ fun _ => le_rfl)
  have hi := spectralABLBareKernel_integrable _ hH m n hX
  unfold spectralABLBareKernel
  apply tendsto_integral_filter_of_dominated_convergence
    (fun t : ℝ => ‖spectralWeylIntegerSignMultiplier m n t X *
      spectralJForwardSpectralWeight f (t : ℂ)‖)
  · apply Eventually.of_forall
    intro L
    exact (spectralWeylIntegerSignMultiplier_measurable m n X).aestronglyMeasurable.mul
      (spectralJRegularizedWeight_real_contDiff f hf.continuous hc hp L).continuous.aestronglyMeasurable
  · apply (eventually_ge_atTop (0 : ℝ)).mono
    intro L hL
    exact ae_of_all _ fun t => by
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left (spectralJRegularizedWeight_real_norm_le f L hL t) (norm_nonneg _)
  · exact hi.norm
  · exact ae_of_all _ fun t => tendsto_const_nhds.mul (spectralJRegularizedWeight_real_tendsto f t)

end
end ArtinMatthews
