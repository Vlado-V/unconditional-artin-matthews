module

public import ArtinMatthews.GiantSignedSourceDoubledVisit
public import ArtinMatthews.GiantSignedWordDomain
public import ArtinMatthews.GiantSignedStateGhostGrowth
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

/-! The doubled absolute ghost visit preserves the original full-memory
domain and pending symmetry. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ} {M : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]

theorem giantSignedSourceDoubledVisit_exponential
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ) (qi ρ : ℝ)
    (f : GiantSignedState PS PB M → ℂ) (hf : GiantSignedWordExponential f) :
    GiantSignedWordExponential (giantSignedSourceDoubledVisit PS ν V qi ρ f) := by
  obtain ⟨U, u, hU, hu, h⟩ := hf
  obtain ⟨U', u', hU', hu', hg⟩ := giantSignedStateGhostApply_exponential PS ν hν
    (fun _ => (|qi / ρ ^ 2| : ℝ)) (fun g => (2 * |-(1-qi) * V g / ρ| : ℝ))
    (fun _ => (|-(1-qi) / ρ| : ℝ)) f U u hU hu (fun s a m => h (s,a,m))
  exact ⟨U', u', hU', hu', fun ⟨s,a,m⟩ => hg s a m⟩

theorem giantSignedSourceDoubledVisit_memorySymmetric
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ) (qi ρ : ℝ)
    (f : GiantSignedState PS PB M → ℂ) (hf : GiantSignedWordExponential f)
    (hsym : ∀ s a, GiantSignedMemorySymmetric (fun m => f (s,a,m))) :
    ∀ s a, GiantSignedMemorySymmetric (fun m => giantSignedSourceDoubledVisit PS ν V qi ρ f (s,a,m)) := by
  obtain ⟨U, u, hU, hu, h⟩ := hf
  exact giantSignedStateGhostApply_memorySymmetric PS ν hν
    (fun _ => (|qi / ρ ^ 2| : ℝ)) (fun g => (2 * |-(1-qi) * V g / ρ| : ℝ))
    (fun _ => (|-(1-qi) / ρ| : ℝ)) f hsym U u hU hu (fun s a m => h (s,a,m))

end
end ArtinMatthews
