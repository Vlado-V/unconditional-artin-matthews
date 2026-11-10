module

public import ArtinMatthews.SpectralKLDirectDefinitions
public import ArtinMatthews.SpectralKLWeightedMeasures
public import ArtinMatthews.SpectralKLDirectBounds
public import ArtinMatthews.SpectralKLDirectDerivatives
public import ArtinMatthews.SpectralKLDirectL2
public import ArtinMatthews.SpectralKLDirectSmallBound
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
open scoped ContDiff
noncomputable section

theorem spectralKLDirectSynthesis_nonpositive_zero (F : ℝ → ℂ) (x : ℝ) (hx : x ≤ 0) :
    spectralKLDirectSynthesis F x = 0 := by
  simp only [spectralKLDirectSynthesis, ite_eq_right (not_lt.mpr hx)]

/-- Regularity and both endpoint bounds for the physical KL profile. -/
def SpectralKLHeatRegularity (f : ℝ → ℂ) : Prop :=
  ContDiffOn ℝ ∞ f (Ioi (0 : ℝ)) ∧ MemLp f 2 spectralKLPhysicalMeasure ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → ‖f x‖ ≤ C * x ^ (3 / 4 : ℝ)) ∧
    (∀ k : ℕ, 1 < k → ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ‖f x‖ ≤ C / x ^ k)

theorem spectralKLDirectSynthesis_regularity (F : ℂ → ℂ)
    (heven : ∀ z : ℂ, F (-z) = F z)
    (hsmooth : ContDiff ℝ ∞ (fun t : ℝ => F (t : ℂ)))
    (hhol : ∀ z : ℂ, |z.im| ≤ 3 / 4 → DifferentiableAt ℂ F z)
    (hrapid : SpectralKLDirectStripRapid F) :
    SpectralKLHeatRegularity (spectralKLDirectSynthesis (fun t : ℝ => F (t : ℂ))) := by
  have hR := spectralKLDirectStripRapid_real hrapid
  have hh (z : ℂ) (hz0 : 0 ≤ z.im) (hzB : z.im ≤ 3 / 4) :=
    hhol z (by rw [abs_of_nonneg hz0]; exact hzB)
  exact ⟨spectralKLDirectSynthesis_contDiffOn _ hsmooth.continuous hR,
    spectralKLDirectSynthesis_memLp _ hsmooth.contDiffOn hsmooth.continuous hR,
    spectralKLDirectSynthesis_global_power_bound F heven hh hrapid,
    fun k hk => spectralKLDirectSynthesis_large_bound _ hR k hk⟩

end
end ArtinMatthews
