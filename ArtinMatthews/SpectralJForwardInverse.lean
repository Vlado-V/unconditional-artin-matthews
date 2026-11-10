module

public import ArtinMatthews.SpectralSearsTitchmarsh
public import ArtinMatthews.SpectralJForwardWeylNormalization
public import ArtinMatthews.SpectralJForwardRealSmooth
public import ArtinMatthews.SpectralJForwardRealWeight
public import ArtinMatthews.SpectralJGaussianCompletedCoefficient
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

namespace ArtinMatthews
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem spectralJForwardTransform_inverse (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Ioi (0 : ℝ)) :
    EqOn f (fun x =>
      spectralJWeightedSynthesis (fun r : ℝ => spectralJForwardSpectralWeight f (r : ℂ)) x +
        spectralJOddSynthesis f x) (Ioi (0 : ℝ)) := by
  let H : ℝ → ℂ := fun r => spectralJForwardSpectralWeight f (r : ℂ)
  apply spectralJ_reconstruction_of_completed_analysis f H hf hc hs
    (spectralJForwardSpectralWeight_real_contDiff f hf.continuous hc hs)
    (spectralJForwardSpectralWeight_real_directRapid f hf hc hs)
    (spectralJForwardSpectralWeight_weber_integrable f hf hc hs)
  obtain ⟨hG, hA⟩ := spectralJGaussianTail_normalized_completed_analysis f hf hc hs
  have hrem : spectralJGaussianRemainder f = fun y : ℝ =>
      (1 / (Real.sqrt (8 * Real.pi) : ℂ)) *
        spectralJGaussianTail (spectralJGaussianTransform f) y := by
    funext y
    simp only [spectralJGaussianRemainder, Complex.ofReal_div, Complex.ofReal_one]
  rw [hrem]
  refine ⟨hG, hA.trans ?_⟩
  filter_upwards [spectralKLPositiveWeightMeasure_ae_pos spectralKLPlancherelWeight] with r hr
  exact (spectralJForwardSpectralWeight_real_eq_weyl f hr).symm

theorem spectralJForwardTransform_inverse_apply (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Ioi (0 : ℝ)) {x : ℝ} (hx : 0 < x) :
    f x =
      spectralJWeightedSynthesis (fun r : ℝ => spectralJForwardSpectralWeight f (r : ℂ)) x +
        spectralJOddSynthesis f x :=
  spectralJForwardTransform_inverse f hf hc hs hx

end
end ArtinMatthews
