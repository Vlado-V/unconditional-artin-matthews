module

public import ArtinMatthews.MarkedMemoryIndependentRelabel
public import ArtinMatthews.MarkedMemoryIndependentEdge
public import ArtinMatthews.MarkedMemorySlotRelabel
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

/-! The actual selected outgoing/incoming indices and both slot
permutations are invariant under relabeling. The equality of the free
copied order is literal; it is not an assumed matching correspondence. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {A A' : J → Type*}
  [∀ j, DecidableEq (A j)] [∀ j, Fintype (A j)]
  [∀ j, DecidableEq (A' j)] [∀ j, Fintype (A' j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (e : (j : J) → A j ≃ A' j)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)

theorem markedMemoryIndependentRelabel_outgoing (v : ℕ) (hv : v < n) (j : J) :
    markedMemoryIndependentOutgoing hZ (markedMemoryIndependentRelabel hZ e d) v hv j =
      markedMemoryIndependentOutgoing hZ d v hv j := by
  apply (d.activeId v j).injective
  apply (e j).injective
  have h := markedMemoryIndependentOutgoing_eq hZ (markedMemoryIndependentRelabel hZ e d) v hv j
  exact h.trans (congrArg (e j) (markedMemoryIndependentOutgoing_eq hZ d v hv j)).symm

theorem markedMemoryIndependentRelabel_incoming (v : ℕ) (hv : v < n) (j : J) :
    markedMemoryIndependentIncoming hZ (markedMemoryIndependentRelabel hZ e d) v hv j =
      markedMemoryIndependentIncoming hZ d v hv j := by
  apply (d.activeId (v+1) j).injective
  apply (e j).injective
  have h := markedMemoryIndependentIncoming_eq hZ (markedMemoryIndependentRelabel hZ e d) v hv j
  exact h.trans (congrArg (e j) (markedMemoryIndependentIncoming_eq hZ d v hv j)).symm

theorem markedMemoryIndependentRelabel_slotPair (v : ℕ) (hv : v < n)
    (order : J → Equiv.Perm (Fin pads)) (j : J) :
    (markedMemoryIndependentSlotPairs hZ (markedMemoryIndependentRelabel hZ e d) v hv order j).1 =
      (markedMemoryIndependentSlotPairs hZ d v hv order j).1 := by
  change markedMemorySlotPairOfOrder _ _ _ _ _ (order j) = markedMemorySlotPairOfOrder _ _ _ _ _ (order j)
  calc
    _ = markedMemorySlotPairOfOrder ((d.activeId v j).trans (e j).toEmbedding)
        ((d.activeId (v+1) j).trans (e j).toEmbedding)
        (markedMemoryIndependentOutgoing hZ d v hv j) (markedMemoryIndependentIncoming hZ d v hv j)
        (markedMemoryRelabel_remaining (e j) (d.activeId v j) (d.activeId (v+1) j)
          (markedMemoryIndependentOutgoing hZ d v hv j) (markedMemoryIndependentIncoming hZ d v hv j)
          (markedMemoryIndependentActive_remaining hZ d v hv j)) (order j) := by
      apply markedMemorySlotPairOfOrder_congr_indices
      · exact markedMemoryIndependentRelabel_outgoing hZ e d v hv j
      · exact markedMemoryIndependentRelabel_incoming hZ e d v hv j
    _ = _ := markedMemorySlotPairOfOrder_relabel (e j) (d.activeId v j) (d.activeId (v+1) j)
      (markedMemoryIndependentOutgoing hZ d v hv j) (markedMemoryIndependentIncoming hZ d v hv j)
      (markedMemoryIndependentActive_remaining hZ d v hv j) (order j)

theorem markedMemoryIndependentRelabel_sourceSlots (v : ℕ) (hv : v < n)
    (order : J → Equiv.Perm (Fin pads)) :
    markedMemoryIndependentSourceSlots hZ (markedMemoryIndependentRelabel hZ e d) v hv order =
      markedMemoryIndependentSourceSlots hZ d v hv order := by
  funext j
  exact congrArg Prod.fst (markedMemoryIndependentRelabel_slotPair hZ e d v hv order j)

theorem markedMemoryIndependentRelabel_targetSlots (v : ℕ) (hv : v < n)
    (order : J → Equiv.Perm (Fin pads)) :
    markedMemoryIndependentTargetSlots hZ (markedMemoryIndependentRelabel hZ e d) v hv order =
      markedMemoryIndependentTargetSlots hZ d v hv order := by
  funext j
  exact congrArg Prod.snd (markedMemoryIndependentRelabel_slotPair hZ e d v hv order j)

theorem markedMemoryIndependentRelabel_rawSource (v : ℕ) (hv : v < n)
    (order : J → Equiv.Perm (Fin pads)) :
    markedRawSlotEquiv (markedMemoryIndependentSourceSlots hZ (markedMemoryIndependentRelabel hZ e d) v hv order)
      (markedMemoryIndependentPostGhost hZ (markedMemoryIndependentRelabel hZ e d) v (Nat.le_of_lt hv)) =
    markedRawSlotEquiv (markedMemoryIndependentSourceSlots hZ d v hv order)
      (markedMemoryIndependentPostGhost hZ d v (Nat.le_of_lt hv)) := by
  rw [markedMemoryIndependentRelabel_sourceSlots, markedMemoryIndependentRelabel_postGhost]

end
end ArtinMatthews
