module

public import ArtinMatthews.RoughBonferroniDivisors
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

/-! Exact support and divisor scale of the finite complex truncation. -/
namespace ArtinMatthews

/-- Prime subsets of size at most `r` have squarefree positive divisors,
bounded by `v^r` when every sieving prime is at most `v`. -/
theorem roughTruncationSubsets_support (P : Finset ℕ) (r v : ℕ)
    (hv : 1 ≤ v) (hprime : ∀ p ∈ P, p.Prime) (hheight : ∀ p ∈ P, p ≤ v)
    (S : Finset ℕ) (hS : S ∈ roughTruncationSubsets P r) :
    0 < roughSubsetDivisor S ∧ Squarefree (roughSubsetDivisor S) ∧
      roughSubsetDivisor S ≤ v ^ r := by
  have hSP : S ⊆ P := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
  have hcard : S.card ≤ r := (Finset.mem_filter.mp hS).2
  refine ⟨roughSubsetDivisor_pos S (fun p hp => hprime p (hSP hp)), ?_⟩
  exact OAI.Erdos970.NumberTheoryLean.BonferroniBlocks.coefficient_divisor_support P
    hv hprime hheight hcard (Finset.mem_powersetCard.mpr ⟨hSP, rfl⟩)

end ArtinMatthews
