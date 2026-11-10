module

public import ArtinMatthews.SpectralKLPhysicalCompactData
public import ArtinMatthews.SpectralKLUnitary
public import ArtinMatthews.SpectralKLCompactInverse
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
noncomputable section

theorem spectralKLBoundedMultiplier_memLp (f : Lp ℂ 2 spectralKLPhysicalMeasure)
    (h : ℝ → ℂ) (hm : AEStronglyMeasurable h spectralKLSpectralMeasure)
    (C : ℝ) (hb : ∀ t, ‖h t‖ ≤ C) :
    MemLp (fun t => h t * spectralKLAnalysis f t) 2 spectralKLSpectralMeasure := by
  apply (Lp.memLp (spectralKLAnalysis f)).of_le_mul (c := C)
    (hm.mul (Lp.aestronglyMeasurable _))
  exact Eventually.of_forall (fun t => by
    change ‖h t * spectralKLAnalysis f t‖ ≤ C * ‖spectralKLAnalysis f t‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hb t) (norm_nonneg _))

/-- The actual inverse unitary KL transform of bounded spectral multiplication. -/
def spectralKLBoundedMultiplierProfile (f : Lp ℂ 2 spectralKLPhysicalMeasure)
    (h : ℝ → ℂ) (hm : AEStronglyMeasurable h spectralKLSpectralMeasure)
    (C : ℝ) (hb : ∀ t, ‖h t‖ ≤ C) : Lp ℂ 2 spectralKLPhysicalMeasure :=
  spectralKLCompletedSynthesis
    ((spectralKLBoundedMultiplier_memLp f h hm C hb).toLp
      (fun t => h t * spectralKLAnalysis f t))

theorem spectralKLBoundedMultiplierProfile_analysis (f : Lp ℂ 2 spectralKLPhysicalMeasure)
    (h : ℝ → ℂ) (hm : AEStronglyMeasurable h spectralKLSpectralMeasure)
    (C : ℝ) (hb : ∀ t, ‖h t‖ ≤ C) :
    spectralKLAnalysis (spectralKLBoundedMultiplierProfile f h hm C hb) =
      (spectralKLBoundedMultiplier_memLp f h hm C hb).toLp
        (fun t => h t * spectralKLAnalysis f t) :=
  spectralKLAnalysis_synthesis _

theorem spectralKLBoundedMultiplierProfile_analysis_ae (f : Lp ℂ 2 spectralKLPhysicalMeasure)
    (h : ℝ → ℂ) (hm : AEStronglyMeasurable h spectralKLSpectralMeasure)
    (C : ℝ) (hb : ∀ t, ‖h t‖ ≤ C) :
    spectralKLAnalysis (spectralKLBoundedMultiplierProfile f h hm C hb) =ᵐ[spectralKLSpectralMeasure]
      (fun t => h t * spectralKLAnalysis f t) := by
  rw [spectralKLBoundedMultiplierProfile_analysis]
  exact MemLp.coeFn_toLp _

theorem spectralKLBoundedMultiplierProfile_compact_analysis
    (g : ℝ → ℂ) (hg : Continuous g) (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi (0 : ℝ))
    (h : ℝ → ℂ) (hm : AEStronglyMeasurable h spectralKLSpectralMeasure)
    (C : ℝ) (hb : ∀ t, ‖h t‖ ≤ C) :
    spectralKLAnalysis (spectralKLBoundedMultiplierProfile
      ((spectralKLPhysical_compact_memLp g hg hc hp).toLp g) h hm C hb) =ᵐ[spectralKLSpectralMeasure]
      (fun t => h t * ∫ x in Ioi (0 : ℝ),
        OAI.CubicEisenstein.schlafliBesselK ((t : ℂ) * Complex.I) x * g x / (x : ℂ)) := by
  filter_upwards [spectralKLBoundedMultiplierProfile_analysis_ae
    ((spectralKLPhysical_compact_memLp g hg hc hp).toLp g) h hm C hb,
    spectralKLAnalysis_compact_integral_ae g hg hc hp] with t hmul htransform
  rw [hmul, htransform]

end
end ArtinMatthews
