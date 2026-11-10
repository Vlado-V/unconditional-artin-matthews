module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.Targets

open Filter
open scoped Topology

noncomputable def representationCount (A : Set ℕ) (n : ℕ) : ℕ := by
  classical
  exact ((Finset.range (n + 1)).filter fun a => a ∈ A ∧ n - a ∈ A).card

noncomputable def orderedRepresentations (A : Set ℕ) (n : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.range (n + 1)).product (Finset.range (n + 1))).filter
    fun r => r.1 ∈ A ∧ r.2 ∈ A ∧ r.1 + r.2 = n

theorem representationCount_eq_card_orderedRepresentations (A : Set ℕ) (n : ℕ) :
    representationCount A n = (orderedRepresentations A n).card := by
  classical
  unfold representationCount orderedRepresentations
  apply Finset.card_bij (fun a _ => (a, n - a))
  · intro a ha
    obtain ⟨harange, haA, hbA⟩ := Finset.mem_filter.mp ha
    have han := Finset.mem_range.mp harange
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨harange, Finset.mem_range.mpr (by omega)⟩,
      haA, hbA, ?_⟩
    omega
  · intro a₁ _ a₂ _ heq
    exact congrArg Prod.fst heq
  · intro r hr
    obtain ⟨hrange, hxA, hyA, hsum⟩ := Finset.mem_filter.mp hr
    have hxrange := (Finset.mem_product.mp hrange).1
    have hdiff : n - r.1 = r.2 := by omega
    refine ⟨r.1, Finset.mem_filter.mpr ⟨hxrange, hxA, ?_⟩, ?_⟩
    · simpa only [hdiff] using hyA
    · exact Prod.ext rfl hdiff

def LogarithmicRepresentationLimit : Prop :=
  ∃ A : Set ℕ, ∃ c : ℝ, c ≠ 0 ∧
    Tendsto (fun n : ℕ => (representationCount A n : ℝ) / Real.log n)
      atTop (𝓝 c)

def AdditiveBasisPiLimit : Prop :=
  ∃ A : Set ℕ,
    Tendsto (fun n : ℕ => (representationCount A n : ℝ) / Real.log n)
      atTop (𝓝 Real.pi)

theorem public_limit_of_pi_limit (h : AdditiveBasisPiLimit) :
    LogarithmicRepresentationLimit := by
  obtain ⟨A, hA⟩ := h
  exact ⟨A, Real.pi, ne_of_gt Real.pi_pos, hA⟩

end NumberTheoryLean.Targets

end

end Erdos970

end OAI
