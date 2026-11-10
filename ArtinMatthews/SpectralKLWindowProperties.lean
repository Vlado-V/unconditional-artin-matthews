module

public import ArtinMatthews.SpectralKLInverseIEnvelope
public import ArtinMatthews.SpectralKLWindowContinuation
public import ArtinMatthews.SpectralKLWindowSmallBound
public import ArtinMatthews.SpectralKLWindowSynthesisBounds
public import ArtinMatthews.SpectralKLWindowSynthesisL2
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory Complex
open scoped ContDiff
noncomputable section

theorem spectralKLWindowSynthesis_properties (h : ℂ → ℂ) (g : ℝ → ℂ)
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi (0 : ℝ))
    (heven : ∀ z : ℂ, h (-z) = h z)
    (hsmooth : ContDiff ℝ ∞ (fun t : ℝ => h (t : ℂ)))
    (hhol : ∀ z : ℂ, |z.im| ≤ 3 / 4 → DifferentiableAt ℂ h z)
    (C₀ : ℝ) (hbounded : ∀ t : ℝ, ‖h (t : ℂ)‖ ≤ C₀)
    (H : ℝ) (hH : 0 ≤ H)
    (hstrip : ∀ t y : ℝ, 0 ≤ y → y ≤ 3 / 4 →
      ‖h ((t : ℂ) + (y : ℂ) * I)‖ ≤ H * (1 + t ^ 2)) :
    ContinuousOn (spectralKLWindowSynthesis h g) (Ioi (0 : ℝ)) ∧
      MemLp (spectralKLWindowSynthesis h g) 2 spectralKLPhysicalMeasure ∧
      (∃ C : ℝ, 0 ≤ C ∧
        (∀ x : ℝ, 0 < x → ‖spectralKLWindowSynthesis h g x‖ ≤ C * x ^ (3 / 4 : ℝ)) ∧
        (∀ x : ℝ, 1 ≤ x → ‖spectralKLWindowSynthesis h g x‖ ≤ C / x ^ 2)) ∧
      (∀ ν : ℂ, |ν.re| ≤ 1 / 2 →
        spectralKLCompactOrderTransform (spectralKLWindowSynthesis h g) ν =
          h (-I * ν) * spectralKLCompactOrderTransform g ν) := by
  have hline (t : ℝ) : ‖h (t : ℂ)‖ ≤ H * (1 + t ^ 2) := by
    simpa only [Complex.ofReal_zero, zero_mul, add_zero] using hstrip t 0 le_rfl (by norm_num)
  have hh (z : ℂ) (hz0 : 0 ≤ z.im) (hzB : z.im ≤ 3 / 4) :=
    hhol z (by rw [abs_of_nonneg hz0]; exact hzB)
  obtain ⟨S, hS, hs⟩ := spectralKLWindowSynthesis_global_power_bound h g hg hc hp heven hh H hH hstrip
  obtain ⟨L, hL, hl⟩ := spectralKLWindowSynthesis_large_bound h g hg hc hp H hH hline 2 (by norm_num)
  refine ⟨spectralKLWindowSynthesis_continuousOn h g hsmooth.continuous hg hc hp H hH hline,
    spectralKLWindowSynthesis_memLp h g hsmooth C₀ hbounded hg hc hp, ?_,
    spectralKLWindowSynthesis_continued_transform h g hg hc hp heven hsmooth hhol C₀ hbounded H hH hstrip⟩
  refine ⟨S + L, add_nonneg hS hL, ?_, ?_⟩
  · intro x hx
    exact (hs x hx).trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  · intro x hx
    exact (hl x hx).trans (div_le_div_of_nonneg_right (by linarith) (sq_nonneg x))

end
end ArtinMatthews
