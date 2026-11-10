module

public import ArtinMatthews.MarkedMemoryHistoryEdgeAccess
public import ArtinMatthews.MarkedMemoryIndependentHistory
public import ArtinMatthews.MarkedMemoryIndependentTraceState
public import ArtinMatthews.MarkedMemoryTransitionDeterminismAccessors
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

/-! Literal finite vertex accessors for an independently reconstructed
history. Promotion is exactly membership of the incoming identity in the
old pending queue; all source-state transports are explicit. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)

theorem markedMemoryGhostTarget_eq_of_heq {s t : MarkedRawState P (pads+1) B Z} (hs : s = t)
    (a : MarkedMemoryGhostChoice hZ s) (b : MarkedMemoryGhostChoice hZ t) (h : HEq a b) :
    markedMemoryGhostChoiceTarget hZ s a = markedMemoryGhostChoiceTarget hZ t b := by
  cases hs
  have he : a = b := eq_of_heq h
  cases he
  rfl

theorem markedMemoryEdge_targetSlots_of_heq {s t : MarkedRawState P (pads+1) B Z} (hs : s = t)
    (a : MarkedMemoryEdgeChoice hZ s) (b : MarkedMemoryEdgeChoice hZ t) (h : HEq a b) :
    a.2.2 = b.2.2 := by
  cases hs
  have he : a = b := eq_of_heq h
  cases he
  rfl

theorem markedMemoryEdge_promoted_of_heq {s t : MarkedRawState P (pads+1) B Z} (hs : s = t)
    (a : MarkedMemoryEdgeChoice hZ s) (b : MarkedMemoryEdgeChoice hZ t) (h : HEq a b) (j : J) :
    a.2.1.promotions j ≠ none ↔ b.2.1.promotions j ≠ none := by
  cases hs
  have he : a = b := eq_of_heq h
  cases he
  rfl

theorem markedMemoryEdgeTransport_targetSlots {s t : MarkedRawState P (pads+1) B Z} (hs : s = t)
    (a : MarkedMemoryEdgeChoice hZ s) : (markedMemoryEdgeTransport hZ hs a).2.2 = a.2.2 := by
  cases hs
  rfl

theorem markedMemoryEdgeTransport_promoted {s t : MarkedRawState P (pads+1) B Z} (hs : s = t)
    (a : MarkedMemoryEdgeChoice hZ s) (j : J) :
    (markedMemoryEdgeTransport hZ hs a).2.1.promotions j ≠ none ↔ a.2.1.promotions j ≠ none := by
  cases hs
  rfl

variable {A : J → Type*} [∀ j, DecidableEq (A j)] [∀ j, Fintype (A j)] {n : ℕ}
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (order : Fin n → J → Equiv.Perm (Fin pads))

local notation "history" => markedMemoryIndependentHistory hZ d order

theorem markedMemoryIndependent_vertex_state (v : Fin (n+1)) :
    markedMemoryHistoryVertexState hZ history v = markedMemoryIndependentState hZ d v.val (by omega) :=
  (markedMemoryHistoryVertexState_trace hZ history v).symm.trans
    (markedMemoryIndependentHistory_trace_even hZ d order v.val (by omega))

theorem markedMemoryIndependent_vertex_ghost_heq (v : Fin (n+1)) :
    HEq (markedMemoryHistoryVertexGhost hZ history v) (markedMemoryIndependentGhost hZ d v.val (by omega)) :=
  markedMemoryFiniteTransitions_history_vertexGhost hZ (markedMemoryIndependentTransitions hZ d order) v

theorem markedMemoryIndependent_vertex_edge_source (v : Fin n) :
    markedMemoryGhostChoiceTarget hZ (markedMemoryHistoryVertexState hZ history v.castSucc)
        (markedMemoryHistoryVertexGhost hZ history v.castSucc) =
      markedMemoryGhostChoiceTarget hZ (markedMemoryIndependentState hZ d v.val (Nat.le_of_lt v.2))
        (markedMemoryIndependentGhost hZ d v.val (Nat.le_of_lt v.2)) :=
  markedMemoryGhostTarget_eq_of_heq hZ (markedMemoryIndependent_vertex_state hZ d order v.castSucc)
    _ _ (markedMemoryIndependent_vertex_ghost_heq hZ d order v.castSucc)

theorem markedMemoryIndependent_vertex_edge_targetSlots (v : Fin n) :
    (markedMemoryHistoryVertexEdge hZ history v).2.2 =
      markedMemoryIndependentTargetSlots hZ d v.val v.2 (order v) := by
  have h := markedMemoryEdge_targetSlots_of_heq hZ
    (markedMemoryIndependent_vertex_edge_source hZ d order v) _ _
    (markedMemoryFiniteTransitions_history_vertexEdge hZ (markedMemoryIndependentTransitions hZ d order) v)
  exact h.trans (markedMemoryEdgeTransport_targetSlots hZ _ _)

theorem markedMemoryIndependentRaw_promoted_iff_mem (v : Fin n) (j : J) :
    (markedMemoryIndependentRawEdge hZ d v.val v.2 (order v)).promotions j ≠ none ↔
      (d.lifespan j).incoming (2*v.val+1) ∈ markedMemoryIndependentQueue hZ d (2*v.val+1) j := by
  constructor
  · intro hn
    obtain ⟨k,hk⟩ := Option.ne_none_iff_exists'.mp hn
    exact List.mem_iff_get.mpr ⟨k,(markedMemoryEdgeQueuePromotion_eq_some
      (markedMemoryIndependentQueue hZ d (2*v.val+1))
      (markedMemoryIndependentQueue_nodup hZ d (2*v.val+1) (by omega))
      (fun j => (d.lifespan j).incoming (2*v.val+1)) j k).mp hk⟩
  · intro hm
    obtain ⟨k,hk⟩ := List.mem_iff_get.mp hm
    have hp := (markedMemoryEdgeQueuePromotion_eq_some
      (markedMemoryIndependentQueue hZ d (2*v.val+1))
      (markedMemoryIndependentQueue_nodup hZ d (2*v.val+1) (by omega))
      (fun j => (d.lifespan j).incoming (2*v.val+1)) j k).mpr hk
    have hp' : (markedMemoryIndependentRawEdge hZ d v.val v.2 (order v)).promotions j = some k := hp
    rw [hp']
    exact Option.some_ne_none k

theorem markedMemoryIndependent_vertex_promoted_iff_mem (v : Fin n) (j : J) :
    (markedMemoryHistoryVertexEdge hZ history v).2.1.promotions j ≠ none ↔
      (d.lifespan j).incoming (2*v.val+1) ∈ markedMemoryIndependentQueue hZ d (2*v.val+1) j := by
  exact (markedMemoryEdge_promoted_of_heq hZ
    (markedMemoryIndependent_vertex_edge_source hZ d order v) _ _
    (markedMemoryFiniteTransitions_history_vertexEdge hZ (markedMemoryIndependentTransitions hZ d order) v) j).trans
      ((markedMemoryEdgeTransport_promoted hZ _ _ j).trans
        (markedMemoryIndependentRaw_promoted_iff_mem hZ d order v j))

end
end ArtinMatthews
