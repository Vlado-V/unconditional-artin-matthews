module

public import ArtinMatthews.SpectralABLCorrectedWindows
public import ArtinMatthews.SpectralKLInverseIEnvelope
public import ArtinMatthews.SpectralABLCorrectedStripGrowth
public import ArtinMatthews.SpectralABLWindowSmooth
public import ArtinMatthews.SpectralKLWindowProperties
public import ArtinMatthews.SpectralKLWindowReal
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
open scoped ComplexConjugate
noncomputable section

def spectralABLRegularCorrectedProfile (T ε : ℝ) (g : ℝ → ℂ) : ℝ → ℂ :=
  spectralKLWindowSynthesis (spectralABLRegularCorrected T (T ^ (1 - ε))) g

def spectralABLExceptionalCorrectedProfile (a : ℝ) (A : ℕ) (g : ℝ → ℂ) : ℝ → ℂ :=
  spectralKLWindowSynthesis (spectralABLExceptionalCorrected a A) g

theorem spectralABLRegularCorrectedProfile_properties (T ε : ℝ) (hT : 0 < T)
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi (0 : ℝ)) :
    ContinuousOn (spectralABLRegularCorrectedProfile T ε g) (Ioi (0 : ℝ)) ∧
      MemLp (spectralABLRegularCorrectedProfile T ε g) 2 spectralKLPhysicalMeasure ∧
      (∃ C : ℝ, 0 ≤ C ∧
        (∀ x : ℝ, 0 < x → ‖spectralABLRegularCorrectedProfile T ε g x‖ ≤ C * x ^ (3 / 4 : ℝ)) ∧
        (∀ x : ℝ, 1 ≤ x → ‖spectralABLRegularCorrectedProfile T ε g x‖ ≤ C / x ^ 2)) ∧
      (∀ ν : ℂ, |ν.re| ≤ 1 / 2 →
        spectralKLCompactOrderTransform (spectralABLRegularCorrectedProfile T ε g) ν =
          spectralABLRegularCorrected T (T ^ (1 - ε)) (-I * ν) * spectralKLCompactOrderTransform g ν) := by
  let Δ := T ^ (1 - ε)
  have hΔ : 0 < Δ := Real.rpow_pos_of_pos hT _
  obtain ⟨H, hH, hb⟩ := spectralABLRegularCorrected_strip_bound T Δ hT hΔ
  have hbounded (t : ℝ) : ‖spectralABLRegularCorrected T Δ (t : ℂ)‖ ≤ H := by
    simpa only [Complex.ofReal_zero, zero_mul, add_zero] using hb t 0 (by norm_num)
  have hstrip (t y : ℝ) (hy0 : 0 ≤ y) (hyB : y ≤ 3 / 4) :
      ‖spectralABLRegularCorrected T Δ ((t : ℂ) + (y : ℂ) * I)‖ ≤ H * (1 + t ^ 2) :=
    (hb t y (by rwa [abs_of_nonneg hy0])).trans
      (le_mul_of_one_le_right hH (by nlinarith [sq_nonneg t]))
  have hhol (z : ℂ) (hz : |z.im| ≤ 3 / 4) : DifferentiableAt ℂ (spectralABLRegularCorrected T Δ) z :=
    spectralABLRegularCorrected_differentiableAt T Δ z (hz.trans_lt (by norm_num))
  simpa only [spectralABLRegularCorrectedProfile, Δ] using
    spectralKLWindowSynthesis_properties (spectralABLRegularCorrected T Δ) g hg hc hp
      (spectralABLRegularCorrected_even T Δ) (spectralABLRegularCorrected_real_contDiff T Δ)
      hhol H hbounded H hH hstrip

theorem spectralABLExceptionalCorrectedProfile_properties (a : ℝ) (A : ℕ) (hA : 1 ≤ A)
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi (0 : ℝ)) :
    ContinuousOn (spectralABLExceptionalCorrectedProfile a A g) (Ioi (0 : ℝ)) ∧
      MemLp (spectralABLExceptionalCorrectedProfile a A g) 2 spectralKLPhysicalMeasure ∧
      (∃ C : ℝ, 0 ≤ C ∧
        (∀ x : ℝ, 0 < x → ‖spectralABLExceptionalCorrectedProfile a A g x‖ ≤ C * x ^ (3 / 4 : ℝ)) ∧
        (∀ x : ℝ, 1 ≤ x → ‖spectralABLExceptionalCorrectedProfile a A g x‖ ≤ C / x ^ 2)) ∧
      (∀ ν : ℂ, |ν.re| ≤ 1 / 2 →
        spectralKLCompactOrderTransform (spectralABLExceptionalCorrectedProfile a A g) ν =
          spectralABLExceptionalCorrected a A (-I * ν) * spectralKLCompactOrderTransform g ν) := by
  obtain ⟨H, hH, hb⟩ := spectralABLExceptionalCorrected_strip_bound a hA
  have hbounded (t : ℝ) : ‖spectralABLExceptionalCorrected a A (t : ℂ)‖ ≤ H := by
    simpa only [Complex.ofReal_zero, zero_mul, add_zero] using hb t 0 (by norm_num)
  have hstrip (t y : ℝ) (hy0 : 0 ≤ y) (hyB : y ≤ 3 / 4) :
      ‖spectralABLExceptionalCorrected a A ((t : ℂ) + (y : ℂ) * I)‖ ≤ H * (1 + t ^ 2) :=
    (hb t y (by rwa [abs_of_nonneg hy0])).trans
      (le_mul_of_one_le_right hH (by nlinarith [sq_nonneg t]))
  have hhol (z : ℂ) (hz : |z.im| ≤ 3 / 4) : DifferentiableAt ℂ (spectralABLExceptionalCorrected a A) z :=
    spectralABLExceptionalCorrected_differentiableAt a hA z (hz.trans_lt (by norm_num))
  simpa only [spectralABLExceptionalCorrectedProfile] using
    spectralKLWindowSynthesis_properties (spectralABLExceptionalCorrected a A) g hg hc hp
      (spectralABLExceptionalCorrected_even a A) (spectralABLExceptionalCorrected_real_contDiff a hA)
      hhol H hbounded H hH hstrip

theorem spectralABLRegularCorrectedProfile_real (T ε : ℝ) (g : ℝ → ℂ)
    (hp : tsupport g ⊆ Ioi (0 : ℝ)) (hg : ∀ x : ℝ, star (g x) = g x) (x : ℝ) :
    star (spectralABLRegularCorrectedProfile T ε g x) = spectralABLRegularCorrectedProfile T ε g x := by
  apply spectralKLWindowSynthesis_real _ g hp hg
  intro t
  change conj _ = _
  rw [spectralABLRegularCorrected_real, spectralABLRegularWindow_real]
  simp only [map_div₀, conj_ofReal]

theorem spectralABLExceptionalCorrectedProfile_real (a : ℝ) (A : ℕ) (g : ℝ → ℂ)
    (hp : tsupport g ⊆ Ioi (0 : ℝ)) (hg : ∀ x : ℝ, star (g x) = g x) (x : ℝ) :
    star (spectralABLExceptionalCorrectedProfile a A g x) = spectralABLExceptionalCorrectedProfile a A g x := by
  apply spectralKLWindowSynthesis_real _ g hp hg
  intro t
  change conj _ = _
  rw [spectralABLExceptionalCorrected_real, spectralABLExceptionalWindow_real]
  simp only [map_div₀, conj_ofReal]

end
end ArtinMatthews
