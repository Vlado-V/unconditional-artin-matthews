module

public import ArtinMatthews.SpectralCuspFourierODEHorizontal
public import ArtinMatthews.SpectralCuspMass
public import ArtinMatthews.SpectralHorizontalPeriodPartition
public import ArtinMatthews.SpectralSeparableTestSeed
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

/-! Actual compact smooth Fourier tests.  The horizontal partition is supported
in two periods and has translates summing to one on a single period. -/

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff MatrixGroups

namespace ArtinMatthews

def cuspFourierTestHorizontal (w : ℝ) (n : ℤ) (x : ℝ) : ℂ :=
  (spectralHorizontalPartition w x : ℂ) * star (cuspFourierPhase w n x)

theorem cuspFourierTestHorizontal_contDiff (w : ℝ) (n : ℤ) :
    ContDiff ℝ ∞ (cuspFourierTestHorizontal w n) := by
  unfold cuspFourierTestHorizontal
  exact (Complex.ofRealCLM.contDiff.comp (spectralHorizontalPartition_contDiff w)).mul
    (Complex.conjCLE.contDiff.comp (cuspFourierPhase_contDiff w n))

theorem cuspFourierTestHorizontal_tsupport (w : ℝ) (n : ℤ) :
    tsupport (cuspFourierTestHorizontal w n) ⊆ tsupport (spectralHorizontalPartition w) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  apply subset_tsupport
  intro hzero
  exact hx (by simp [cuspFourierTestHorizontal, hzero])

theorem cuspFourierTestHorizontal_compact {w : ℝ} (hw : 0 < w) (n : ℤ) :
    HasCompactSupport (cuspFourierTestHorizontal w n) :=
  (spectralHorizontalPartition_hasCompactSupport hw).of_isClosed_subset
    (isClosed_tsupport _) (cuspFourierTestHorizontal_tsupport w n)

def cuspFourierTestSeed (w : ℝ) (hw : 0 < w) (n : ℤ) (ρ : ℝ → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpos : tsupport ρ ⊆ Ioi (0 : ℝ)) : h2SmoothCompactSeeds :=
  h2SeparableSmoothSeed (cuspFourierTestHorizontal w n) (fun y => (ρ y : ℂ))
    (cuspFourierTestHorizontal_contDiff w n) (Complex.ofRealCLM.contDiff.comp hρ)
    (cuspFourierTestHorizontal_compact hw n) (hcρ.comp_left Complex.ofReal_zero)
    ((tsupport_comp_subset Complex.ofReal_zero ρ).trans hpos)

theorem cuspFourierTestSeed_apply (w : ℝ) (hw : 0 < w) (n : ℤ) (ρ : ℝ → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpos : tsupport ρ ⊆ Ioi (0 : ℝ)) (z : UpperHalfPlane) :
    (cuspFourierTestSeed w hw n ρ hρ hcρ hpos).val z =
      (spectralHorizontalPartition w z.re * ρ z.im : ℝ) *
        star (cuspFourierPhase w n z.re) := by
  change ((spectralHorizontalPartition w z.re : ℂ) * star (cuspFourierPhase w n z.re)) *
    (ρ z.im : ℂ) = _
  rw [Complex.ofReal_mul]
  ring

theorem cuspFourierTestSeed_support (w : ℝ) (hw : 0 < w) (n : ℤ) (ρ : ℝ → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpos : tsupport ρ ⊆ Ioi (0 : ℝ)) (Y : ℝ) (hs : tsupport ρ ⊆ Ioi Y) :
    Function.support (fun z : UpperHalfPlane =>
      (cuspFourierTestSeed w hw n ρ hρ hcρ hpos).val z) ⊆
      hyperbolicCuspStrip (2 * w) Y := by
  intro z hz
  change (cuspFourierTestSeed w hw n ρ hρ hcρ hpos).val z ≠ 0 at hz
  rw [cuspFourierTestSeed_apply] at hz
  have hn := (mul_ne_zero_iff.mp hz).1
  have hp : spectralHorizontalPartition w z.re * ρ z.im ≠ 0 :=
    Complex.ofReal_ne_zero.mp hn
  have hx := (mul_ne_zero_iff.mp hp).1
  have hy := (mul_ne_zero_iff.mp hp).2
  refine ⟨⟨?_, ?_⟩, hs (subset_tsupport ρ hy)⟩
  · by_contra h
    exact hx (spectralHorizontalPartition_zero_left hw (le_of_not_gt h))
  · exact (spectralHorizontalPartition_tsupport hw (subset_tsupport _ hx)).2

end ArtinMatthews
