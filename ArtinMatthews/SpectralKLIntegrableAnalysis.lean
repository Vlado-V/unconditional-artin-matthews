module

public import ArtinMatthews.SpectralKLAnalysisIntegral
public import ArtinMatthews.SpectralKLKernelOrderContinuity
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

/-! Literal KL analysis for noncompact physical inputs with an actual
integrable K0 majorant.  No compact-support inference is made. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein
open scoped Topology

namespace ArtinMatthews

def spectralKLIntegrableMajorant (f : ℝ → ℂ) (x : ℝ) : ℝ :=
  spectralKLRealKernel 0 x*‖spectralKLPhysicalCompactDiv f x‖

theorem spectralKLIntegrableMajorant_bound (f : ℝ → ℂ)
    (hfzero : ∀ x : ℝ, x ≤ 0 → f x = 0) (t x : ℝ) :
    ‖(spectralKLRealKernel t x : ℂ)*spectralKLPhysicalCompactDiv f x‖ ≤
      spectralKLIntegrableMajorant f x := by
  by_cases hx : 0 < x
  · rw [norm_mul,Complex.norm_real]
    exact mul_le_mul_of_nonneg_right (spectralKLRealKernel_norm_le_zero t hx) (norm_nonneg _)
  · simp [spectralKLPhysicalCompactDiv,spectralKLIntegrableMajorant,hfzero x (le_of_not_gt hx)]

theorem spectralKLAnalysis_integrable_of_majorant (f : ℝ → ℂ) (hf : Measurable f)
    (hfzero : ∀ x : ℝ, x ≤ 0 → f x = 0) (hM : Integrable (spectralKLIntegrableMajorant f)) (t : ℝ) :
    Integrable (fun x : ℝ => (spectralKLRealKernel t x : ℂ)*spectralKLPhysicalCompactDiv f x) := by
  have hK : Measurable (fun x : ℝ => (spectralKLRealKernel t x : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp spectralKLRealKernel_stronglyMeasurable.measurable
      |>.comp (measurable_const.prodMk measurable_id)
  have hD : Measurable (spectralKLPhysicalCompactDiv f) := by
    unfold spectralKLPhysicalCompactDiv
    fun_prop
  exact hM.mono' (hK.mul hD).aestronglyMeasurable
    (Filter.Eventually.of_forall (spectralKLIntegrableMajorant_bound f hfzero t))

theorem spectralKLAnalysis_continuous_of_majorant (f : ℝ → ℂ) (hf : Measurable f)
    (hfzero : ∀ x : ℝ, x ≤ 0 → f x = 0) (hM : Integrable (spectralKLIntegrableMajorant f)) :
    Continuous (spectralKLPhysicalAnalysisIntegral f) := by
  unfold spectralKLPhysicalAnalysisIntegral
  apply continuous_of_dominated (bound := spectralKLIntegrableMajorant f)
  · intro t
    exact (spectralKLAnalysis_integrable_of_majorant f hf hfzero hM t).aestronglyMeasurable
  · intro t
    exact Filter.Eventually.of_forall (spectralKLIntegrableMajorant_bound f hfzero t)
  · exact hM
  · filter_upwards with x
    by_cases hx : 0 < x
    · exact (Complex.continuous_ofReal.comp (spectralKLRealKernel_order_continuous hx)).mul continuous_const
    · simpa only [spectralKLPhysicalCompactDiv,hfzero x (le_of_not_gt hx),zero_div,mul_zero] using
        (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))

theorem spectralKLAnalysis_integral_of_nonpositive_zero (f : ℝ → ℂ)
    (hfzero : ∀ x : ℝ, x ≤ 0 → f x = 0) (t : ℝ) :
    spectralKLPhysicalAnalysisIntegral f t =
      ∫ x in Ioi (0 : ℝ), schlafliBesselK ((t : ℂ)*Complex.I) x*f x/(x : ℂ) := by
  unfold spectralKLPhysicalAnalysisIntegral
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ)) (fun x hx => ?_)]
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [schlafliBesselK_imaginary_eq_realKernel t hx]
    simp only [spectralKLPhysicalCompactDiv,mul_div_assoc]
  · simp [spectralKLPhysicalCompactDiv,hfzero x (le_of_not_gt hx)]

end ArtinMatthews
