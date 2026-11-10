module

public import ArtinMatthews.MarkedMemoryActualFibers
public import ArtinMatthews.MarkedMemoryHistoryLifespanScalarEvents
public import ArtinMatthews.MarkedMemoryPopulationTransport
public import ArtinMatthews.MarkedMemoryGhostOriginLists
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
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The actual ghost source, survivor and birth labels in their literal
pending-slot order. Deletions are exactly the computed last endpoints. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
  (history : MarkedMemoryChronologicalHistory hZ n s)

local notation "vertex" v:max => markedMemoryHistoryVertexState hZ history v
local notation "ghost" v:max => markedMemoryHistoryVertexGhost hZ history v
local notation "target" v:max => markedMemoryGhostChoiceTarget hZ (vertex v) (ghost v)

theorem markedMemoryPopulationStateCast_group {s t : MarkedRawState P (pads+1) B Z}
    (h : s = t) (i : MarkedMemoryPopulationIndex s) :
    markedMemoryPopulationGroup t (markedMemoryPopulationStateCast h i) = markedMemoryPopulationGroup s i := by
  cases h
  rfl

def markedMemoryActualGhostTargetOrigin (v : Fin (n+1)) (i : MarkedMemoryPopulationIndex (target v)) :
    MarkedMemoryHistoryTraceAddress hZ history :=
  markedMemoryActualOrigin hZ history ((markedMemoryHistoryGhostTime n v)+1) (markedMemoryHistoryGhostTargetIndex hZ history v i)

theorem markedMemoryActualGhostOrigin (v : Fin (n+1)) (i : MarkedMemoryPopulationIndex (target v)) :
    Sum.elim (markedMemoryHistoryGhostSourceOrigin hZ history v)
      (fun b => markedMemoryHistoryGhostScalarOrigin hZ history ⟨v,Sum.inr b⟩)
      (markedMemoryGhostPopulationOrigin hZ (vertex v) (ghost v) i) =
        markedMemoryActualGhostTargetOrigin hZ history v i := by
  unfold markedMemoryActualGhostTargetOrigin markedMemoryActualOrigin
  change _ = Sum.elim _ _ (markedMemoryHistoryTraceStep hZ history ((markedMemoryHistoryGhostTime n v))
    (markedMemoryHistoryGhostTargetIndex hZ history v i))
  rw [markedMemoryHistoryGhostStep]
  cases markedMemoryGhostPopulationOrigin hZ (vertex v) (ghost v) i <;> rfl

def markedMemoryActualGhostSourceIds (v : Fin (n+1)) (j : J) :
    Fin ((vertex v).2.2.1.1 j : ℕ) → MarkedMemoryActualFiber hZ history j := fun k =>
  ⟨markedMemoryHistoryGhostSourceOrigin hZ history v (Sum.inr ⟨j,k⟩),by
    exact (markedMemoryHistoryTraceOrigin_group hZ history ((markedMemoryHistoryGhostTime n v))
      (markedMemoryHistoryGhostSourceIndex hZ history v (Sum.inr ⟨j,k⟩))).trans
      (markedMemoryPopulationStateCast_group
        (markedMemoryHistoryTraceState_stage hZ history (markedMemoryHistoryVertexStage n v)).symm (Sum.inr ⟨j,k⟩))⟩

def markedMemoryActualGhostTargetIds (v : Fin (n+1)) (j : J) :
    Fin ((target v).2.2.1.1 j : ℕ) → MarkedMemoryActualFiber hZ history j := fun k =>
  ⟨markedMemoryActualGhostTargetOrigin hZ history v (Sum.inr ⟨j,k⟩),by
    exact (markedMemoryHistoryTraceOrigin_group hZ history ((markedMemoryHistoryGhostTime n v)+1)
      (markedMemoryHistoryGhostTargetIndex hZ history v (Sum.inr ⟨j,k⟩))).trans
      (markedMemoryPopulationStateCast_group
        (markedMemoryHistoryGhostTarget_trace hZ history v).symm (Sum.inr ⟨j,k⟩))⟩

def markedMemoryActualGhostBirthIds (v : Fin (n+1)) (j : J)
    (k : Fin ((ghost v).sizes.1 j : ℕ)) : MarkedMemoryActualFiber hZ history j :=
  markedMemoryActualGhostTargetIds hZ history v j
    ((markedMemoryGhostOrigin (vertex v).2.2 (ghost v).deletion (ghost v).sizes j).symm (Sum.inr k))

theorem markedMemoryActualGhostBirthIds_val (v : Fin (n+1)) (j : J)
    (k : Fin ((ghost v).sizes.1 j : ℕ)) :
    (markedMemoryActualGhostBirthIds hZ history v j k).1 =
      markedMemoryHistoryGhostScalarOrigin hZ history ⟨v,Sum.inr ⟨j,k⟩⟩ := by
  have h := markedMemoryActualGhostOrigin hZ history v (Sum.inr
    ⟨j,(markedMemoryGhostOrigin (vertex v).2.2 (ghost v).deletion (ghost v).sizes j).symm (Sum.inr k)⟩)
  rw [markedMemoryGhostPopulationOrigin_birth] at h
  exact h.symm

theorem markedMemoryActualGhostSourceIds_list (v : Fin (n+1)) (j : J) :
    List.ofFn (markedMemoryActualGhostSourceIds hZ history v j) =
      markedMemoryActualPendingQueue hZ history ((markedMemoryHistoryGhostTime n v)) j := by
  apply (List.map_injective_iff (f := Subtype.val)).mpr Subtype.val_injective
  simp only [List.map_ofFn, markedMemoryActualPendingQueue]
  exact markedMemoryPopulationStateCast_pending_list
    (markedMemoryHistoryTraceState_stage hZ history (markedMemoryHistoryVertexStage n v)).symm
    (markedMemoryActualOrigin hZ history ((markedMemoryHistoryGhostTime n v))) j

theorem markedMemoryActualGhostTargetIds_list (v : Fin (n+1)) (j : J) :
    List.ofFn (markedMemoryActualGhostTargetIds hZ history v j) =
      markedMemoryActualPendingQueue hZ history ((markedMemoryHistoryGhostTime n v)+1) j := by
  apply (List.map_injective_iff (f := Subtype.val)).mpr Subtype.val_injective
  simp only [List.map_ofFn, markedMemoryActualPendingQueue]
  exact markedMemoryPopulationStateCast_pending_list (markedMemoryHistoryGhostTarget_trace hZ history v).symm
    (markedMemoryActualOrigin hZ history ((markedMemoryHistoryGhostTime n v)+1)) j

theorem markedMemoryActualGhost_survivor (v : Fin (n+1)) (j : J)
    (k : ↥(markedRawGhostSurvivors (vertex v).2.2 (ghost v).deletion j)) :
    markedMemoryActualGhostTargetIds hZ history v j
      ((markedMemoryGhostOrigin (vertex v).2.2 (ghost v).deletion (ghost v).sizes j).symm (Sum.inl k)) =
        markedMemoryActualGhostSourceIds hZ history v j k.1 := by
  apply Subtype.ext
  have h := markedMemoryActualGhostOrigin hZ history v (Sum.inr
    ⟨j,(markedMemoryGhostOrigin (vertex v).2.2 (ghost v).deletion (ghost v).sizes j).symm (Sum.inl k)⟩)
  rw [markedMemoryGhostPopulationOrigin_old] at h
  exact h.symm

theorem markedMemoryActualGhost_deleted_iff (v : Fin (n+1)) (j : J)
    (k : Fin ((vertex v).2.2.1.1 j : ℕ)) :
    k ∈ (ghost v).deletion j ↔
      markedMemoryActualLast hZ history j (markedMemoryActualGhostSourceIds hZ history v j k) = (markedMemoryHistoryGhostTime n v) := by
  constructor
  · exact markedMemoryHistoryGhost_deleted_last hZ history v j k
  · intro hlast
    by_contra hn
    have hk : k ∈ markedRawGhostSurvivors (vertex v).2.2 (ghost v).deletion j := by
      simpa only [markedRawGhostSurvivors,Finset.mem_sdiff,Finset.mem_univ,true_and] using hn
    have he := congrArg Subtype.val (markedMemoryActualGhost_survivor hZ history v j ⟨k,hk⟩)
    have hbound : (markedMemoryHistoryGhostTime n v)+1 ≤ 2*n+1 := by
      rw [markedMemoryHistoryGhostTime_eq]
      have hv := v.isLt
      omega
    have hp := (markedMemoryHistory_lifespan_exact hZ history
      (markedMemoryActualGhostSourceIds hZ history v j k).1 ((markedMemoryHistoryGhostTime n v)+1)).mp
      ⟨hbound,markedMemoryHistoryGhostTargetIndex hZ history v (Sum.inr
        ⟨j,(markedMemoryGhostOrigin (vertex v).2.2 (ghost v).deletion (ghost v).sizes j).symm (Sum.inl ⟨k,hk⟩)⟩),he⟩
    have hlastBound := hp.2
    change (markedMemoryHistoryGhostTime n v)+1 ≤ markedMemoryActualLast hZ history j (markedMemoryActualGhostSourceIds hZ history v j k) at hlastBound
    omega

end
end ArtinMatthews
