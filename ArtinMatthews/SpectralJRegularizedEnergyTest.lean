module

public import ArtinMatthews.SpectralJRegularizedWeightBounds
public import ArtinMatthews.SpectralJRegularizerLimit
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

open Set
open scoped ContDiff
noncomputable section

def spectralJRegularizedEnergyTest (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) (L : ℝ) (hL : 0 ≤ L) :
    SpectralEnergyTest :=
  spectralSourceEnergyTest (spectralJRegularizedWeight f L)
    (fun z hz => (spectralJRegularizedWeight_differentiableAt f hf.continuous hc hp L z
      (lt_of_le_of_lt hz (by norm_num))).continuousAt)
    (Classical.choose (spectralJRegularizedWeight_strip_bound f hf hc hp L hL))
    (fun t => by
      simpa only [Complex.ofReal_zero, zero_mul, add_zero] using
        (Classical.choose_spec (spectralJRegularizedWeight_strip_bound f hf hc hp L hL)).2
          t 0 (by norm_num))

theorem spectralJRegularizedEnergyTest_apply (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) (L : ℝ) (hL : 0 ≤ L)
    (l : Ici (0 : ℝ)) :
    spectralJRegularizedEnergyTest f hf hc hp L hL l =
      spectralJRegularizedWeight f L (spectralSourceParameter l) := rfl

theorem spectralJRegularizedEnergyTest_pos (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) (L : ℝ) (hL : 0 ≤ L)
    (l : Ici (0 : ℝ)) (hl : 0 < (l : ℝ)) :
    spectralJRegularizedEnergyTest f hf hc hp L hL l =
      (spectralJRegularizationMultiplier L l : ℂ) *
        spectralJForwardSpectralWeight f (spectralSourceParameter l) := by
  rw [spectralJRegularizedEnergyTest_apply, spectralJRegularizedWeight_source_pos f L l hl]
  rfl

theorem spectralJRegularizedEnergyTest_zero (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) (L : ℝ) (hL : 0 ≤ L) :
    spectralJRegularizedEnergyTest f hf hc hp L hL ⟨0, by norm_num⟩ =
      (L : ℂ) * spectralJForwardTransform f (Complex.I / 2) := by
  rw [spectralJRegularizedEnergyTest_apply, spectralSourceParameter_zero,
    spectralJRegularizedWeight_half_I]

theorem spectralJRegularizedEnergyTest_continuous_symbol (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) (L : ℝ) (hL : 0 ≤ L)
    (t : ℝ) :
    spectralContinuousTestSymbol (spectralJRegularizedEnergyTest f hf hc hp L hL) t =
      spectralJRegularizedWeight f L (t : ℂ) := by
  apply spectralSourceEnergyTest_continuous_symbol
  exact spectralJRegularizedWeight_even f L

theorem spectralJRegularizedWeight_source_tendsto (f : ℝ → ℂ) (l : ℝ) (hl : 0 < l) :
    Filter.Tendsto (fun L : ℝ => spectralJRegularizedWeight f L (spectralSourceParameter l))
      Filter.atTop (nhds (spectralJForwardSpectralWeight f (spectralSourceParameter l))) := by
  have h := ((Complex.continuous_ofReal.tendsto 1).comp
    (spectralJRegularizationMultiplier_tendsto hl)).mul_const
      (spectralJForwardSpectralWeight f (spectralSourceParameter l))
  simpa only [spectralJRegularizedWeight_source_pos f _ l hl,
    spectralJRegularizationMultiplier, Complex.ofReal_one, one_mul, Function.comp_def] using h

theorem spectralJRegularizedEnergyTest_pos_norm_le (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) (L : ℝ) (hL : 0 ≤ L)
    (l : Ici (0 : ℝ)) (hl : 0 < (l : ℝ)) :
    ‖spectralJRegularizedEnergyTest f hf hc hp L hL l‖ ≤
      ‖spectralJForwardSpectralWeight f (spectralSourceParameter l)‖ := by
  rw [spectralJRegularizedEnergyTest_pos f hf hc hp L hL l hl, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
      (spectralJRegularizationMultiplier_bounds hL hl.le).1]
  exact mul_le_of_le_one_left (norm_nonneg _) (spectralJRegularizationMultiplier_bounds hL hl.le).2

end
end ArtinMatthews
