module

public import ArtinMatthews.MarkedMemoryActualSlotOrder
public import ArtinMatthews.MarkedMemoryRawEdgeRecovery
public import ArtinMatthews.MarkedMemoryActualEdgeQueueOrigins
public import ArtinMatthews.MarkedMemoryActualStateReconstruction
public import ArtinMatthews.MarkedMemoryQueueOriginLabels
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

/-! Recover the literal raw edge fields from the actual extracted
tableau. Source equality transports dependent promotion indices; the
ordered queue identifies those indices without numeric-prime injectivity. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
  (history : MarkedMemoryChronologicalHistory hZ n s)
  (ha : MarkedMemoryHistoryAnchorAdmissible hZ history) (v : Fin n)

local notation "tableau" => markedMemoryActualTableau hZ history ha
local notation "order" => markedMemoryActualOrder hZ history ha v
local notation "edge" => markedMemoryHistoryVertexEdge hZ history v
local notation "source" => markedMemoryGhostChoiceTarget hZ
  (markedMemoryHistoryVertexState hZ history v.castSucc) (markedMemoryHistoryVertexGhost hZ history v.castSucc)
local notation "rebuilt" => markedMemoryIndependentRawEdge hZ tableau (Fin.val v) (Fin.isLt v) order
local notation "time" => 2*v.val+1

theorem markedMemoryActualTableau_edgeSource :
    markedMemoryIndependentPostGhost hZ tableau v.val (Nat.le_of_lt v.2) = source :=
  (markedMemoryActualTableau_postGhost hZ history ha v.val (Nat.le_of_lt v.2)).trans
    (markedMemoryHistoryEdgeSource_trace hZ history v)

theorem markedMemoryActualRawEdge_source :
    markedRawSlotEquiv (markedMemoryIndependentSourceSlots hZ tableau v.val v.2 order)
      (markedMemoryIndependentPostGhost hZ tableau v.val (Nat.le_of_lt v.2)) =
        markedRawSlotEquiv edge.1 source := by
  rw [markedMemoryActualOrder_sourceSlots, markedMemoryActualTableau_edgeSource]

def markedMemoryActualRawEdgeTransported : MarkedRawEdgeChoice hZ (markedRawSlotEquiv edge.1 source) :=
  markedMemoryRawEdgeTransport hZ (markedMemoryActualRawEdge_source hZ history ha v) rebuilt

theorem markedMemoryActualRawEdge_target :
    (markedMemoryActualRawEdgeTransported hZ history ha v).target = edge.2.1.target := by
  rw [markedMemoryActualRawEdgeTransported, markedMemoryRawEdgeTransport_target]
  exact congrArg Prod.fst (markedMemoryHistoryEdgeTarget_trace hZ history v)

theorem markedMemoryActualRawEdge_store :
    (markedMemoryActualRawEdgeTransported hZ history ha v).store = edge.2.1.store := by
  rw [markedMemoryActualRawEdgeTransported, markedMemoryRawEdgeTransport_store]
  funext j
  change decide (time < markedMemoryActualLast hZ history j (markedMemoryActualOutgoingAt hZ history time j)) = _
  rw [markedMemoryActualOutgoingAt_edge]
  exact (markedMemoryActualEdge_store_eq_decide_last hZ history v j).symm

theorem markedMemoryActualRawEdge_promotions :
    (markedMemoryActualRawEdgeTransported hZ history ha v).promotions = edge.2.1.promotions := by
  funext j
  apply Option.ext
  intro k
  rw [markedMemoryActualRawEdgeTransported, markedMemoryRawEdgeTransport_promotions_some]
  apply Iff.trans ?_ (markedMemoryActualEdge_promote_iff hZ history v j k).symm
  let k' : Fin (markedMemoryIndependentQueue hZ tableau time j).length :=
    Fin.cast (congrArg (fun q : MarkedRawState P (pads+1) B Z => (q.2.2.1.1 j : ℕ))
      (markedMemoryActualRawEdge_source hZ history ha v).symm) k
  change (rebuilt).promotions j = some k' ↔ _
  rw [show (rebuilt).promotions j = some k' ↔
      (markedMemoryIndependentQueue hZ tableau time j).get k' =
        ((tableau).lifespan j).incoming time from
    markedMemoryEdgeQueuePromotion_eq_some (markedMemoryIndependentQueue hZ tableau time)
      (markedMemoryIndependentQueue_nodup hZ tableau time (by omega))
      (fun j => ((tableau).lifespan j).incoming time) j k']
  have hqueue : List.ofFn (markedMemoryActualEdgeSourcePendingIds hZ history v j) =
      markedMemoryIndependentQueue hZ tableau time j :=
    (markedMemoryActualEdgeSourcePendingIds_list hZ history v j).trans
      (markedMemoryActualTableau_queue hZ history ha time (by omega) j).symm
  have hget := markedMemoryListGet_ofFn_eq (markedMemoryActualEdgeSourcePendingIds hZ history v j)
    (markedMemoryIndependentQueue hZ tableau time j) hqueue k'
  have hget' : (markedMemoryIndependentQueue hZ tableau time j).get k' =
      markedMemoryActualEdgeSourcePendingIds hZ history v j k := by
    refine hget.trans ?_
    exact congrArg (markedMemoryActualEdgeSourcePendingIds hZ history v j) (Fin.ext rfl)
  change (markedMemoryIndependentQueue hZ tableau time j).get k' =
    markedMemoryActualIncomingAt hZ history time j ↔ _
  rw [markedMemoryActualIncomingAt_edge, hget']

theorem markedMemoryActualRawEdge_last :
    markedRawEdgeTargetLast (markedRawSlotEquiv edge.1 source).2.2
      (markedMemoryActualRawEdgeTransported hZ history ha v).promotions
      (markedMemoryActualRawEdgeTransported hZ history ha v).fresh =
      markedRawEdgeTargetLast (markedRawSlotEquiv edge.1 source).2.2 edge.2.1.promotions edge.2.1.fresh := by
  rw [markedMemoryActualRawEdgeTransported, markedMemoryRawEdgeTransport_last]
  change markedRawEdgeTargetLast (markedMemoryIndependentMemory hZ tableau time (by omega))
    (rebuilt).promotions (rebuilt).fresh = _
  rw [markedMemoryIndependentRawEdge_last hZ tableau v.val v.2 order]
  funext j
  rw [markedMemoryActualTableau_incoming]
  have hp := congrArg Sigma.fst (markedMemoryActualParticle_active hZ history ha
    (2*(v.val+1)) j ((edge.2.2 j).symm (Fin.last pads)))
  have ht := congrArg (fun q : MarkedRawState P (pads+1) B Z =>
    q.2.1 j ((edge.2.2 j).symm (Fin.last pads))) (markedMemoryHistoryEdgeTarget_trace hZ history v)
  refine hp.trans (ht.trans ?_)
  change (markedRawEdgeTargetState hZ (markedRawSlotEquiv edge.1 source) edge.2.1).2.1 j
    (edge.2.2 j ((edge.2.2 j).symm (Fin.last pads))) = _
  rw [Equiv.apply_symm_apply]
  have hs : ((markedRawActiveSplit pads)
      (markedRawEdgeTargetState hZ (markedRawSlotEquiv edge.1 source) edge.2.1).2.1).2 =
      markedRawEdgeTargetLast (markedRawSlotEquiv edge.1 source).2.2 edge.2.1.promotions edge.2.1.fresh := by
    change ((markedRawActiveSplit pads) ((markedRawActiveSplit pads).symm _)).2 = _
    rw [Equiv.apply_symm_apply]
  exact congrArg (fun f => f j) hs

theorem markedMemoryActualRawEdge_eq :
    markedMemoryActualRawEdgeTransported hZ history ha v = edge.2.1 :=
  markedMemoryRawEdgeChoice_eq_of_last hZ _ _
    (markedMemoryActualRawEdge_target hZ history ha v)
    (markedMemoryActualRawEdge_store hZ history ha v)
    (markedMemoryActualRawEdge_promotions hZ history ha v)
    (markedMemoryActualRawEdge_last hZ history ha v)

theorem markedMemoryActualRawEdge_heq : HEq rebuilt edge.2.1 :=
  (markedMemoryRawEdgeTransport_heq hZ (markedMemoryActualRawEdge_source hZ history ha v) rebuilt).trans
    (heq_of_eq (markedMemoryActualRawEdge_eq hZ history ha v))

end
end ArtinMatthews
