module

public import ArtinMatthews.SpectralABLHeatProfiles
public import ArtinMatthews.SpectralKLUnitary
public import ArtinMatthews.SpectralABLCorrectedStripGrowth
public import ArtinMatthews.SpectralABLWindowSmooth
public import ArtinMatthews.SpectralKLDirectL2
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

/-! The completed KL analysis of the actual direct heat profiles is
their literal Gaussian spectral datum. -/

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff
namespace ArtinMatthews

theorem spectralKLDirectSynthesis_completed_analysis (F : ℝ → ℂ)
    (hF : ContDiffOn ℝ ∞ F (Ioi (0 : ℝ))) (hFc : Continuous F)
    (hrapid : SpectralKLDirectRapid F)
    (hL : MemLp (spectralKLDirectSynthesis F) 2 spectralKLPhysicalMeasure) :
    spectralKLAnalysis (hL.toLp (spectralKLDirectSynthesis F)) =ᵐ[spectralKLSpectralMeasure] F := by
  have hd := spectralKLDirectData_memLp F hFc hrapid
  have hi := spectralKLDirectSynthesis_inverse_ae F hF hFc hrapid
  have he : hL.toLp (spectralKLDirectSynthesis F) = spectralKLCompletedSynthesis (hd.toLp F) := by
    apply Lp.ext
    exact hL.coeFn_toLp.trans hi.symm
  rw [he,spectralKLAnalysis_synthesis]
  exact hd.coeFn_toLp

theorem spectralKLHeatProfile_completed_analysis (R : ℝ) (hR : 0 < R)
    (hL : MemLp (spectralKLHeatProfile R) 2 spectralKLPhysicalMeasure) :
    spectralKLAnalysis (hL.toLp (spectralKLHeatProfile R)) =ᵐ[spectralKLSpectralMeasure]
      fun t : ℝ => spectralKLGaussianData R (t : ℂ) := by
  have hs := spectralKLGaussianData_real_contDiff R
  exact spectralKLDirectSynthesis_completed_analysis _ hs.contDiffOn hs.continuous
    (spectralKLDirectStripRapid_real (spectralKLGaussianData_direct_rapid R hR)) hL

theorem spectralKLWeightedHeatProfile_completed_analysis (h : ℂ → ℂ) (R : ℝ) (hR : 0 < R)
    (hs : ContDiff ℝ ∞ (fun t : ℝ => h (t : ℂ))) (H : ℝ) (hH : 0 ≤ H)
    (hb : ∀ t y : ℝ, |y| ≤ 3/4 → ‖h ((t : ℂ)+(y : ℂ)*Complex.I)‖ ≤ H)
    (hL : MemLp (spectralKLWeightedHeatProfile h R) 2 spectralKLPhysicalMeasure) :
    spectralKLAnalysis (hL.toLp (spectralKLWeightedHeatProfile h R)) =ᵐ[spectralKLSpectralMeasure]
      fun t : ℝ => spectralKLGaussianWeightedData h R (t : ℂ) := by
  have hdata := spectralKLGaussianWeightedData_real_contDiff h R hs
  exact spectralKLDirectSynthesis_completed_analysis _ hdata.contDiffOn hdata.continuous
    (spectralKLDirectStripRapid_real (spectralKLGaussianWeightedData_direct_rapid h R hR H hH hb)) hL

theorem spectralABLRegularHeatProfile_completed_analysis (T ε R : ℝ) (hT : 0 < T) (hR : 0 < R)
    (hL : MemLp (spectralABLRegularHeatProfile T ε R) 2 spectralKLPhysicalMeasure) :
    spectralKLAnalysis (hL.toLp (spectralABLRegularHeatProfile T ε R)) =ᵐ[spectralKLSpectralMeasure]
      fun t : ℝ => spectralKLGaussianWeightedData (spectralABLRegularCorrected T (T^(1-ε))) R (t : ℂ) := by
  obtain ⟨H,hH,hb⟩ := spectralABLRegularCorrected_strip_bound T (T^(1-ε)) hT (Real.rpow_pos_of_pos hT _)
  exact spectralKLWeightedHeatProfile_completed_analysis _ R hR
    (spectralABLRegularCorrected_real_contDiff T (T^(1-ε))) H hH hb hL

theorem spectralABLExceptionalHeatProfile_completed_analysis (a : ℝ) (A : ℕ) (R : ℝ)
    (hA : 1 ≤ A) (hR : 0 < R)
    (hL : MemLp (spectralABLExceptionalHeatProfile a A R) 2 spectralKLPhysicalMeasure) :
    spectralKLAnalysis (hL.toLp (spectralABLExceptionalHeatProfile a A R)) =ᵐ[spectralKLSpectralMeasure]
      fun t : ℝ => spectralKLGaussianWeightedData (spectralABLExceptionalCorrected a A) R (t : ℂ) := by
  obtain ⟨H,hH,hb⟩ := spectralABLExceptionalCorrected_strip_bound a hA
  exact spectralKLWeightedHeatProfile_completed_analysis _ R hR
    (spectralABLExceptionalCorrected_real_contDiff a hA) H hH hb hL

end ArtinMatthews
