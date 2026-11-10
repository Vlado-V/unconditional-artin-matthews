module

public import ArtinMatthews.SpectralABLCorrectedWindows
public import ArtinMatthews.SpectralKLWeightedMeasures
public import ArtinMatthews.SpectralABLWindowFirstMoments
public import ArtinMatthews.SpectralABLWindowPositivity
public import ArtinMatthews.SpectralKLCoshIntegrability
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

/-! Actual source windows are integrable in the KL spectral measure
at the parameters needed for the bare diagonal trace. -/

noncomputable section
open Set MeasureTheory
namespace ArtinMatthews

theorem spectralABLRegularCorrected_integrable (T Δ : ℝ) (hT : 0 < T) (hΔ : 0 < Δ) :
    Integrable (fun t : ℝ => spectralABLRegularCorrected T Δ (t : ℂ)) spectralKLSpectralMeasure := by
  apply spectralKLCosh_integrable _ (spectralABLRegularWindowReal T Δ)
  · have he (t : ℝ) : spectralABLRegularCorrected T Δ (t : ℂ) =
        (spectralABLRegularWindowReal T Δ t : ℂ)/(Real.cosh (Real.pi*t) : ℂ) := by
      rw [spectralABLRegularCorrected_real,spectralABLRegularWindow_real]
    simp_rw [he]
    unfold spectralABLRegularWindowReal
    fun_prop
  · exact fun t _ => spectralABLRegularWindowReal_nonneg T Δ t
  · exact spectralABLRegularWindowReal_first_moment_integrable hT hΔ
  · exact fun t _ => (spectralABLRegularCorrected_norm_real T Δ t).le

theorem spectralABLExceptionalCorrected_integrable (a : ℝ) (A : ℕ) (hA : 3 ≤ A) :
    Integrable (fun t : ℝ => spectralABLExceptionalCorrected a A (t : ℂ)) spectralKLSpectralMeasure := by
  apply spectralKLCosh_integrable _ (spectralABLExceptionalWindowReal a A)
  · have he (t : ℝ) : spectralABLExceptionalCorrected a A (t : ℂ) =
        (spectralABLExceptionalWindowReal a A t : ℂ)/(Real.cosh (Real.pi*t) : ℂ) := by
      rw [spectralABLExceptionalCorrected_real,spectralABLExceptionalWindow_real]
    simp_rw [he]
    unfold spectralABLExceptionalWindowReal
    fun_prop
  · exact fun t _ => spectralABLExceptionalWindowReal_nonneg a A t
  · exact spectralABLExceptionalWindowReal_first_moment_integrable a hA
  · exact fun t _ => (spectralABLExceptionalCorrected_norm_real a A t).le

end ArtinMatthews
