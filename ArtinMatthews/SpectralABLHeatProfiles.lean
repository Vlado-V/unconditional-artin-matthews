module

public import ArtinMatthews.SpectralKLHeatProfiles
public import ArtinMatthews.SpectralABLCorrectedWindows
public import ArtinMatthews.SpectralABLCorrectedStripGrowth
public import ArtinMatthews.SpectralABLWindowSmooth
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
open Set MeasureTheory Complex
open scoped ContDiff ComplexConjugate
noncomputable section

def spectralABLRegularHeatProfile (T ε R : ℝ) : ℝ → ℂ :=
  spectralKLWeightedHeatProfile (spectralABLRegularCorrected T (T ^ (1 - ε))) R

def spectralABLExceptionalHeatProfile (a : ℝ) (A : ℕ) (R : ℝ) : ℝ → ℂ :=
  spectralKLWeightedHeatProfile (spectralABLExceptionalCorrected a A) R

theorem spectralABLRegularHeatProfile_properties (T ε R : ℝ) (hT : 0 < T) (hR : 0 < R) :
    SpectralKLHeatRegularity (spectralABLRegularHeatProfile T ε R) := by
  let Δ := T ^ (1 - ε)
  have hΔ : 0 < Δ := Real.rpow_pos_of_pos hT _
  obtain ⟨H, hH, hb⟩ := spectralABLRegularCorrected_strip_bound T Δ hT hΔ
  exact spectralKLWeightedHeatProfile_properties (spectralABLRegularCorrected T Δ) R hR
    (spectralABLRegularCorrected_even T Δ) (spectralABLRegularCorrected_real_contDiff T Δ)
    (fun z hz => spectralABLRegularCorrected_differentiableAt T Δ z (hz.trans_lt (by norm_num))) H hH hb

theorem spectralABLExceptionalHeatProfile_properties (a : ℝ) (A : ℕ) (R : ℝ)
    (hA : 1 ≤ A) (hR : 0 < R) :
    SpectralKLHeatRegularity (spectralABLExceptionalHeatProfile a A R) := by
  obtain ⟨H, hH, hb⟩ := spectralABLExceptionalCorrected_strip_bound a hA
  exact spectralKLWeightedHeatProfile_properties (spectralABLExceptionalCorrected a A) R hR
    (spectralABLExceptionalCorrected_even a A) (spectralABLExceptionalCorrected_real_contDiff a hA)
    (fun z hz => spectralABLExceptionalCorrected_differentiableAt a hA z (hz.trans_lt (by norm_num))) H hH hb

theorem spectralABLRegularHeatProfile_continued_transform (T ε R : ℝ) (hT : 0 < T) (hR : 0 < R)
    (ν : ℂ) (hν : |ν.re| ≤ 1 / 2) :
    spectralKLCompactOrderTransform (spectralABLRegularHeatProfile T ε R) ν =
      spectralABLRegularCorrected T (T ^ (1 - ε)) (-I * ν) * Complex.exp (ν ^ 2 / (R : ℂ) ^ 2) := by
  let Δ := T ^ (1 - ε)
  have hΔ : 0 < Δ := Real.rpow_pos_of_pos hT _
  obtain ⟨H, hH, hb⟩ := spectralABLRegularCorrected_strip_bound T Δ hT hΔ
  exact spectralKLWeightedHeatProfile_continued_transform (spectralABLRegularCorrected T Δ) R hR
    (spectralABLRegularCorrected_even T Δ) (spectralABLRegularCorrected_real_contDiff T Δ)
    (fun z hz => spectralABLRegularCorrected_differentiableAt T Δ z (hz.trans_lt (by norm_num))) H hH hb ν hν

theorem spectralABLExceptionalHeatProfile_continued_transform (a : ℝ) (A : ℕ) (R : ℝ)
    (hA : 1 ≤ A) (hR : 0 < R) (ν : ℂ) (hν : |ν.re| ≤ 1 / 2) :
    spectralKLCompactOrderTransform (spectralABLExceptionalHeatProfile a A R) ν =
      spectralABLExceptionalCorrected a A (-I * ν) * Complex.exp (ν ^ 2 / (R : ℂ) ^ 2) := by
  obtain ⟨H, hH, hb⟩ := spectralABLExceptionalCorrected_strip_bound a hA
  exact spectralKLWeightedHeatProfile_continued_transform (spectralABLExceptionalCorrected a A) R hR
    (spectralABLExceptionalCorrected_even a A) (spectralABLExceptionalCorrected_real_contDiff a hA)
    (fun z hz => spectralABLExceptionalCorrected_differentiableAt a hA z (hz.trans_lt (by norm_num))) H hH hb ν hν

theorem spectralABLRegularHeatProfile_real (T ε R x : ℝ) :
    star (spectralABLRegularHeatProfile T ε R x) = spectralABLRegularHeatProfile T ε R x := by
  apply spectralKLWeightedHeatProfile_real
  intro t
  change conj _ = _
  rw [spectralABLRegularCorrected_real, spectralABLRegularWindow_real]
  simp only [map_div₀, conj_ofReal]

theorem spectralABLExceptionalHeatProfile_real (a : ℝ) (A : ℕ) (R x : ℝ) :
    star (spectralABLExceptionalHeatProfile a A R x) = spectralABLExceptionalHeatProfile a A R x := by
  apply spectralKLWeightedHeatProfile_real
  intro t
  change conj _ = _
  rw [spectralABLExceptionalCorrected_real, spectralABLExceptionalWindow_real]
  simp only [map_div₀, conj_ofReal]

theorem spectralABLRegularHeatProfile_nonpositive_zero (T ε R x : ℝ) (hx : x ≤ 0) :
    spectralABLRegularHeatProfile T ε R x = 0 := spectralKLWeightedHeatProfile_nonpositive_zero _ R x hx

theorem spectralABLExceptionalHeatProfile_nonpositive_zero (a : ℝ) (A : ℕ) (R x : ℝ) (hx : x ≤ 0) :
    spectralABLExceptionalHeatProfile a A R x = 0 := spectralKLWeightedHeatProfile_nonpositive_zero _ R x hx

theorem spectralABLRegularHeatData_strip_uniform (T ε : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R t y : ℝ, 1 ≤ R → |y| ≤ 3 / 4 →
      ‖spectralKLGaussianWeightedData (spectralABLRegularCorrected T (T ^ (1 - ε))) R
        ((t : ℂ) + (y : ℂ) * I)‖ ≤ C := by
  let Δ := T ^ (1 - ε)
  have hΔ : 0 < Δ := Real.rpow_pos_of_pos hT _
  obtain ⟨H, hH, hb⟩ := spectralABLRegularCorrected_strip_bound T Δ hT hΔ
  exact ⟨H * Real.exp (9 / 16 : ℝ), by positivity, fun R t y hR hy =>
    spectralKLGaussianWeightedData_strip_uniform _ R hR H hH hb t y hy⟩

theorem spectralABLExceptionalHeatData_strip_uniform (a : ℝ) (A : ℕ) (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R t y : ℝ, 1 ≤ R → |y| ≤ 3 / 4 →
      ‖spectralKLGaussianWeightedData (spectralABLExceptionalCorrected a A) R
        ((t : ℂ) + (y : ℂ) * I)‖ ≤ C := by
  obtain ⟨H, hH, hb⟩ := spectralABLExceptionalCorrected_strip_bound a hA
  exact ⟨H * Real.exp (9 / 16 : ℝ), by positivity, fun R t y hR hy =>
    spectralKLGaussianWeightedData_strip_uniform _ R hR H hH hb t y hy⟩

end
end ArtinMatthews
