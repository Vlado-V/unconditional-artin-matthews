module

public import ArtinMatthews.MarkedMemoryHistorySlotSchedule
public import ArtinMatthews.MarkedMemoryIndependentHistory
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

/-! Distinct copied-slot orderings give distinct literal histories.
The source permutation at each edge recovers that ordering, so its
factorial multiplicity is proved rather than supplied as a bijection. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)

theorem markedMemoryEdgeTransport_sourceSlots {s t : MarkedRawState P (pads+1) B Z}
    (h : s = t) (edge : MarkedMemoryEdgeChoice hZ s) :
    (markedMemoryEdgeTransport hZ h edge).1 = edge.1 := by
  cases h
  rfl

variable {A : J → Type*} [∀ j, DecidableEq (A j)] [∀ j, Fintype (A j)] {n : ℕ}
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)

theorem markedMemoryIndependentHistory_sourceSlots
    (order : Fin n → J → Equiv.Perm (Fin pads)) (r : Fin n) :
    markedMemoryHistorySourceSlots hZ (markedMemoryIndependentHistory hZ d order) r =
      markedMemoryIndependentSourceSlots hZ d r r.2 (order r) :=
  (markedMemoryFiniteTransitions_history_slots hZ (markedMemoryIndependentTransitions hZ d order) r).trans
    (markedMemoryEdgeTransport_sourceSlots hZ (markedMemoryIndependentGhost_target hZ d r (Nat.le_of_lt r.2)).symm
      (markedMemoryIndependentEdge hZ d r r.2 (order r)))

theorem markedMemoryIndependentSourceSlots_injective (r : ℕ) (hr : r < n) :
    Function.Injective (markedMemoryIndependentSourceSlots hZ d r hr) := by
  intro a b hab
  funext j
  apply Equiv.ext
  intro k
  have hk := congrArg (fun f : J → Equiv.Perm (Fin (pads+1)) => f j k.castSucc) hab
  change markedMemoryOutgoingSlotPermutation (markedMemoryIndependentOutgoing hZ d r hr j) (a j) k.castSucc =
    markedMemoryOutgoingSlotPermutation (markedMemoryIndependentOutgoing hZ d r hr j) (b j) k.castSucc at hk
  rw [markedMemoryOutgoingSlotPermutation_castSucc, markedMemoryOutgoingSlotPermutation_castSucc] at hk
  exact Fin.castSucc_inj.mp ((Equiv.swap (Fin.last pads) (markedMemoryIndependentOutgoing hZ d r hr j)).injective hk)

theorem markedMemoryIndependentHistory_order_injective :
    Function.Injective (markedMemoryIndependentHistory hZ d) := by
  intro a b hab
  funext r
  apply markedMemoryIndependentSourceSlots_injective hZ d r r.2
  exact (markedMemoryIndependentHistory_sourceSlots hZ d a r).symm.trans
    ((congrArg (fun h => markedMemoryHistorySourceSlots hZ h r) hab).trans
      (markedMemoryIndependentHistory_sourceSlots hZ d b r))

def markedMemoryIndependentOrderHistoryEquiv :
    (Fin n → J → Equiv.Perm (Fin pads)) ≃ Set.range (markedMemoryIndependentHistory hZ d) :=
  Equiv.ofInjective (markedMemoryIndependentHistory hZ d) (markedMemoryIndependentHistory_order_injective hZ d)

instance markedMemoryIndependentOrderHistory_fintype :
    Fintype (Set.range (markedMemoryIndependentHistory hZ d)) := by
  classical
  exact Fintype.ofEquiv (Fin n → J → Equiv.Perm (Fin pads)) (markedMemoryIndependentOrderHistoryEquiv hZ d)

theorem markedMemoryIndependentOrderHistory_card :
    Nat.card (Set.range (markedMemoryIndependentHistory hZ d)) =
      (pads.factorial ^ Fintype.card J) ^ n := by
  classical
  rw [← Nat.card_congr (markedMemoryIndependentOrderHistoryEquiv hZ d), Nat.card_eq_fintype_card]
  simp only [Fintype.card_fun, Fintype.card_perm, Fintype.card_fin]

/-- Arbitrary literal history coefficients and target observables can be
reindexed through the proved order-history equivalence without any
symmetry or coefficient-equality assumption. -/
theorem markedMemoryIndependentOrderHistory_sum {R : Type*} [AddCommMonoid R]
    (f : MarkedMemoryChronologicalHistory hZ n (markedMemoryIndependentState hZ d 0 (Nat.zero_le n)) → R) :
    (∑ order : Fin n → J → Equiv.Perm (Fin pads), f (markedMemoryIndependentHistory hZ d order)) =
      ∑ history : Set.range (markedMemoryIndependentHistory hZ d), f history.1 := by
  classical
  exact Equiv.sum_comp (markedMemoryIndependentOrderHistoryEquiv hZ d) (fun history => f history.1)

end
end ArtinMatthews
