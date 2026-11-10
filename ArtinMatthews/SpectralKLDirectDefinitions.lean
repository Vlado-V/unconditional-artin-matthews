module

public import ArtinMatthews.SpectralBesselI
public import ArtinMatthews.SpectralKLCompactIsometry
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

namespace ArtinMatthews
open Set MeasureTheory
noncomputable section

/-- Exponential-normalized rapid decay for data in the genuine KL spectral measure. -/
def SpectralKLDirectRapid (F : ℝ → ℂ) : Prop :=
  ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
    (1 + t ^ 2) ^ N * Real.exp (Real.pi * |t| / 2) * ‖F t‖ ≤ C

/-- The same spectral decay throughout the strip used in the I-kernel shift. -/
def SpectralKLDirectStripRapid (F : ℂ → ℂ) : Prop :=
  ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t y : ℝ, |y| ≤ 3 / 4 →
    (1 + t ^ 2) ^ N * Real.exp (Real.pi * |t| / 2) *
      ‖F ((t : ℂ) + (y : ℂ) * Complex.I)‖ ≤ C

theorem spectralKLDirectStripRapid_real {F : ℂ → ℂ}
    (hF : SpectralKLDirectStripRapid F) :
    SpectralKLDirectRapid (fun t : ℝ => F (t : ℂ)) := by
  intro N
  obtain ⟨C, hC, hb⟩ := hF N
  refine ⟨C, hC, fun t => ?_⟩
  simpa only [Complex.ofReal_zero, zero_mul, add_zero] using hb t 0 (by norm_num)

/-- The normalized inverse KL integral, extended by zero off the positive ray. -/
def spectralKLDirectSynthesis (F : ℝ → ℂ) (x : ℝ) : ℂ :=
  if 0 < x then spectralKLWeightedSynthesis F x else 0

def spectralKLDirectIIntegrand (F : ℂ → ℂ) (x : ℝ) (z : ℂ) : ℂ :=
  z * F z * spectralBesselI (-Complex.I * z) x

end
end ArtinMatthews
