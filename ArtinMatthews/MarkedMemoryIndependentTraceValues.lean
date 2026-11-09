module

public import ArtinMatthews.MarkedMemoryIndependentTraceState
public import ArtinMatthews.MarkedMemoryIndependentGhostLabels


set_option backward.privateInPublic true
@[expose] public section

/-! The bounded actual trace labels agree with the concrete local
vertex/post-ghost identity functions. These transport equations keep
all dependent population casts explicit. -/
namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)

theorem markedMemoryEdgeTransport_origin {s t : MarkedRawState P (pads+1) B Z}
    (h : s = t) (edge : MarkedMemoryEdgeChoice hZ s) :
    HEq (markedMemoryEdgeSlotPopulationOrigin hZ t (markedMemoryEdgeTransport hZ h edge))
      (markedMemoryEdgeSlotPopulationOrigin hZ s edge) := by
  cases h
  rfl

variable {A : J → Type*} [∀ j, DecidableEq (A j)] [∀ j, Fintype (A j)] {n : ℕ}
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (order : Fin n → J → Equiv.Perm (Fin pads))

theorem markedMemoryIndependentTraceIds_even (r : ℕ) (hr : r ≤ n)
    (i : MarkedMemoryPopulationIndex (markedMemoryHistoryTraceState hZ (markedMemoryIndependentHistory hZ d order) (2*r))) :
    markedMemoryIndependentTraceIds hZ d order (2*r) (by omega) i =
      markedMemoryIndependentVertexValue hZ d r hr
        (markedMemoryPopulationStateCast (markedMemoryIndependentHistory_trace_even hZ d order r hr) i) := by
  have hc := markedMemoryPopulationStateCast_trans (markedMemoryIndependentHistory_trace_even hZ d order r hr)
    (markedMemoryIndependentStageState_even hZ d r hr).symm i
  exact (congrArg (markedMemoryIndependentPopulationLabel hZ d (2*r) (by omega)) hc.symm).trans
    (markedMemoryIndependentVertexValue_stage hZ d r hr
      (markedMemoryPopulationStateCast (markedMemoryIndependentHistory_trace_even hZ d order r hr) i))

theorem markedMemoryIndependentTraceIds_odd (r : ℕ) (hr : r ≤ n)
    (i : MarkedMemoryPopulationIndex (markedMemoryHistoryTraceState hZ (markedMemoryIndependentHistory hZ d order) (2*r+1))) :
    markedMemoryIndependentTraceIds hZ d order (2*r+1) (by omega) i =
      markedMemoryIndependentPostGhostValue hZ d r hr
        (markedMemoryPopulationStateCast (markedMemoryIndependentHistory_trace_odd hZ d order r hr) i) := by
  have hc := markedMemoryPopulationStateCast_trans (markedMemoryIndependentHistory_trace_odd hZ d order r hr)
    (markedMemoryIndependentStageState_odd hZ d r hr).symm i
  exact (congrArg (markedMemoryIndependentPopulationLabel hZ d (2*r+1) (by omega)) hc.symm).trans
    (markedMemoryIndependentPostGhostValue_stage hZ d r hr
      (markedMemoryPopulationStateCast (markedMemoryIndependentHistory_trace_odd hZ d order r hr) i))

theorem markedMemoryIndependentTraceIds_even_at (t r : ℕ) (ht : t ≤ 2*n+1) (hr : r ≤ n)
    (htime : t = 2*r)
    (i : MarkedMemoryPopulationIndex (markedMemoryHistoryTraceState hZ (markedMemoryIndependentHistory hZ d order) t)) :
    markedMemoryIndependentTraceIds hZ d order t ht i =
      markedMemoryIndependentVertexValue hZ d r hr
        (markedMemoryPopulationStateCast
          ((congrArg (markedMemoryHistoryTraceState hZ (markedMemoryIndependentHistory hZ d order)) htime).trans
            (markedMemoryIndependentHistory_trace_even hZ d order r hr)) i) := by
  subst t
  exact markedMemoryIndependentTraceIds_even hZ d order r hr i

theorem markedMemoryIndependentHistory_trace_ghostOrigin (r : ℕ) (hr : r ≤ n) :
    HEq (markedMemoryHistoryTraceStep hZ (markedMemoryIndependentHistory hZ d order) (2*r))
      (markedMemoryGhostPopulationOrigin hZ (markedMemoryIndependentState hZ d r hr)
        (markedMemoryIndependentGhost hZ d r hr)) :=
  markedMemoryFiniteTransitions_history_trace_ghostStep hZ (markedMemoryIndependentTransitions hZ d order) r hr

theorem markedMemoryIndependentHistory_trace_edgeOrigin (r : ℕ) (hr : r < n) :
    HEq (markedMemoryHistoryTraceStep hZ (markedMemoryIndependentHistory hZ d order) (2*r+1))
      (markedMemoryEdgeSlotPopulationOrigin hZ (markedMemoryIndependentPostGhost hZ d r (Nat.le_of_lt hr))
        (markedMemoryIndependentEdge hZ d r hr (order ⟨r,hr⟩))) :=
  (markedMemoryFiniteTransitions_history_trace_edgeStep hZ (markedMemoryIndependentTransitions hZ d order) r hr).trans
    (markedMemoryEdgeTransport_origin hZ (markedMemoryIndependentGhost_target hZ d r (Nat.le_of_lt hr)).symm
      (markedMemoryIndependentEdge hZ d r hr (order ⟨r,hr⟩)))

end
end ArtinMatthews
