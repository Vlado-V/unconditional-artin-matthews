module

public import ArtinMatthews.SpectralKLMacdonaldProfile
public import ArtinMatthews.SpectralKLIntegrableAnalysis
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

/-! The noncompact Gaussian-Weyl profile satisfies the actual K0
majorant hypotheses, by the proved zero-order Macdonald product integral. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein

namespace ArtinMatthews

theorem spectralKLMacdonaldProfile_measurable (x y : ℝ) : Measurable (spectralKLMacdonaldProfile x y) :=
  spectralKLExpReciprocal_measurable _ _

theorem spectralKLMacdonaldProfile_nonpositive_zero (x y z : ℝ) (hz : z ≤ 0) :
    spectralKLMacdonaldProfile x y z = 0 := by
  simp only [spectralKLMacdonaldProfile,spectralKLExpReciprocal,ite_eq_right (not_lt.mpr hz)]

theorem spectralKLMacdonaldProfile_majorant_integrable {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Integrable (spectralKLIntegrableMajorant (spectralKLMacdonaldProfile x y)) := by
  let P := spectralKLMacdonaldProfile x y
  have hi : IntegrableOn (fun z : ℝ => ‖schlafliBesselK 0 z*P z/(z : ℂ)‖) (Ioi (0 : ℝ)) := by
    simpa only [Complex.ofReal_zero,zero_mul,P] using! (spectralKLMacdonaldProfile_kernel_integrable hx hy 0).norm
  have hind := (integrable_indicator_iff measurableSet_Ioi).mpr hi
  apply hind.congr
  filter_upwards with z
  by_cases hz : z ∈ Ioi (0 : ℝ)
  · rw [indicator_of_mem hz]
    have hK : schlafliBesselK 0 z = (spectralKLRealKernel 0 z : ℂ) := by
      simpa only [Complex.ofReal_zero,zero_mul] using schlafliBesselK_imaginary_eq_realKernel 0 hz
    change ‖schlafliBesselK 0 z*P z/(z : ℂ)‖ = spectralKLRealKernel 0 z*‖P z/(z : ℂ)‖
    rw [mul_div_assoc,hK,norm_mul,Complex.norm_real,Real.norm_of_nonneg spectralKLRealKernel_zero_nonneg]
  · rw [indicator_of_notMem hz]
    have hz0 : z ≤ 0 := le_of_not_gt hz
    simp only [spectralKLIntegrableMajorant,spectralKLPhysicalCompactDiv,
      spectralKLMacdonaldProfile_nonpositive_zero x y z hz0,zero_div,norm_zero,mul_zero]

theorem spectralKLMacdonaldProfile_literal_analysis {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (t : ℝ) :
    spectralKLPhysicalAnalysisIntegral (spectralKLMacdonaldProfile x y) t =
      2*schlafliBesselK ((t : ℂ)*Complex.I) x*schlafliBesselK ((t : ℂ)*Complex.I) y := by
  rw [spectralKLAnalysis_integral_of_nonpositive_zero _
    (spectralKLMacdonaldProfile_nonpositive_zero x y)]
  exact spectralKLMacdonaldProfile_analysis_integral hx hy t

end ArtinMatthews
