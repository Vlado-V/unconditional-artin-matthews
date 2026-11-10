module

public import ArtinMatthews.MarkedMemoryFiniteHistoryIndex
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

/-! One finite decorated-history index, allowing every band-label count
up to a fixed bound. Each label family is Fin(N_j), so no history-dependent
type family is hidden in the summation domain. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z) (K : ℕ)

abbrev MarkedMemoryBoundedHistoryIndex :=
  Σ counts : J → Fin (K+1),
    MarkedMemoryFiniteHistoryIndex (A := fun j => Fin (counts j : ℕ)) (n := n) hZ s

instance markedMemoryBoundedHistoryIndex_fintype :
    Fintype (MarkedMemoryBoundedHistoryIndex (n := n) hZ s K) := by
  infer_instance

def markedMemoryBoundedHistoryAssembly
    (index : MarkedMemoryBoundedHistoryIndex (n := n) hZ s K) : MarkedMemoryChronologicalHistory hZ n s :=
  markedMemoryFiniteHistoryAssembly hZ s index.2

theorem markedMemoryBoundedHistoryAssembly_fiber_sum {R : Type*} [AddCommMonoid R]
    (F : MarkedMemoryChronologicalHistory hZ n s → R) :
    (∑ index : MarkedMemoryBoundedHistoryIndex (n := n) hZ s K,
      F (markedMemoryBoundedHistoryAssembly hZ s K index)) =
    ∑ history : MarkedMemoryChronologicalHistory hZ n s,
      ∑ _index : {index : MarkedMemoryBoundedHistoryIndex (n := n) hZ s K //
        markedMemoryBoundedHistoryAssembly hZ s K index = history}, F history := by
  have he := Fintype.sum_fiberwise (markedMemoryBoundedHistoryAssembly (n := n) hZ s K)
    (fun index => F (markedMemoryBoundedHistoryAssembly hZ s K index))
  refine he.symm.trans ?_
  apply Finset.sum_congr rfl
  intro history _
  apply Finset.sum_congr rfl
  intro index _
  exact congrArg F index.property

end
end ArtinMatthews
