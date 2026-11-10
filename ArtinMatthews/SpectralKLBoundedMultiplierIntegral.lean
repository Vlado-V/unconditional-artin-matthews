module

public import ArtinMatthews.SpectralKLBoundedMultiplier
public import ArtinMatthews.SpectralKLInverseIEnvelope
public import ArtinMatthews.SpectralKLAnalysisCalibration
public import ArtinMatthews.SpectralKLWindowSynthesisL2
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
open Set MeasureTheory Filter
open scoped ContDiff
noncomputable section

theorem spectralKLBoundedMultiplierProfile_integral_ae (h : ℂ → ℂ) (g : ℝ → ℂ)
    (hh : ContDiff ℝ ∞ (fun t : ℝ => h (t : ℂ))) (C : ℝ)
    (hbound : ∀ t : ℝ, ‖h (t : ℂ)‖ ≤ C)
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi (0 : ℝ)) :
    spectralKLBoundedMultiplierProfile
      ((spectralKLPhysical_compact_memLp g hg.continuous hc hp).toLp g)
      (fun t : ℝ => h (t : ℂ)) hh.continuous.aestronglyMeasurable C hbound
        =ᵐ[spectralKLPhysicalMeasure] spectralKLWindowSynthesis h g := by
  let G : Lp ℂ 2 spectralKLPhysicalMeasure :=
    (spectralKLPhysical_compact_memLp g hg.continuous hc hp).toLp g
  let A := spectralKLBoundedMultiplier_memLp G (fun t : ℝ => h (t : ℂ))
    hh.continuous.aestronglyMeasurable C hbound
  let B := spectralKLWindowData_memLp h g hh.continuous C hbound hg.continuous hc hp
  have heq : A.toLp (fun t : ℝ => h (t : ℂ) * spectralKLAnalysis G t) =
      B.toLp (spectralKLWindowData h g) := by
    apply Lp.ext
    filter_upwards [A.coeFn_toLp, B.coeFn_toLp,
      spectralKLAnalysis_compact_ae g hg.continuous hc hp] with t htA htB htG
    rw [htA, htB]
    rw [htG, spectralKLWindowData, spectralKLCompactOrderTransform_imaginary g hp]
  change spectralKLCompletedSynthesis (A.toLp _) =ᵐ[spectralKLPhysicalMeasure] _
  rw [heq]
  exact spectralKLWindowSynthesis_inverse_ae h g hh C hbound hg hc hp

end
end ArtinMatthews
