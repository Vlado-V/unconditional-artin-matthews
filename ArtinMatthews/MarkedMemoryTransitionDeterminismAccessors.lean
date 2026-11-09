module

public import ArtinMatthews.MarkedMemoryHistoryEdgeAccess
public import ArtinMatthews.MarkedMemoryTransitionTrace


set_option backward.privateInPublic true
@[expose] public section

/-! The actual finite vertex accessors of the deterministic transition
assembler. Heterogeneous equalities retain the dependent choice types
across the source-state transports in every recursive tail. -/
namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)

theorem markedMemoryHistoryTransport_vertexState {n : ℕ}
    {s t : MarkedRawState P (pads+1) B Z} (h : s = t)
    (history : MarkedMemoryChronologicalHistory hZ n s) (v : Fin (n+1)) :
    markedMemoryHistoryVertexState hZ (markedMemoryHistoryTransport hZ h history) v =
      markedMemoryHistoryVertexState hZ history v := by
  cases h
  rfl

theorem markedMemoryHistoryTransport_vertexGhost {n : ℕ}
    {s t : MarkedRawState P (pads+1) B Z} (h : s = t)
    (history : MarkedMemoryChronologicalHistory hZ n s) (v : Fin (n+1)) :
    HEq (markedMemoryHistoryVertexGhost hZ (markedMemoryHistoryTransport hZ h history) v)
      (markedMemoryHistoryVertexGhost hZ history v) := by
  cases h
  rfl

theorem markedMemoryHistoryTransport_vertexEdge {n : ℕ}
    {s t : MarkedRawState P (pads+1) B Z} (h : s = t)
    (history : MarkedMemoryChronologicalHistory hZ n s) (v : Fin n) :
    HEq (markedMemoryHistoryVertexEdge hZ (markedMemoryHistoryTransport hZ h history) v)
      (markedMemoryHistoryVertexEdge hZ history v) := by
  cases h
  rfl

variable {N : ℕ} (d : MarkedMemoryFiniteTransitions (P := P) (pads := pads) (B := B) hZ N)

theorem markedMemoryFiniteTransitions_ghost_congr
    (a b : ℕ) (ha : a ≤ N) (hb : b ≤ N) (h : a = b) :
    HEq (d.ghost a ha) (d.ghost b hb) := by
  subst b
  rfl

theorem markedMemoryFiniteTransitions_edge_congr
    (a b : ℕ) (ha : a < N) (hb : b < N) (h : a = b) :
    HEq (d.edge a ha) (d.edge b hb) := by
  subst b
  rfl

theorem markedMemoryFiniteTransitions_segment_vertexState
    (remaining start : ℕ) (hbound : start+remaining ≤ N) (v : Fin (remaining+1)) :
    markedMemoryHistoryVertexState hZ
      (markedMemoryFiniteTransitions_segment hZ d remaining start hbound) v =
        d.state (start+v.val) (by omega) :=
  (markedMemoryHistoryVertexState_trace hZ _ v).symm.trans
    (markedMemoryFiniteTransitions_segment_trace_even hZ d remaining start hbound v.val (by omega))

theorem markedMemoryFiniteTransitions_segment_vertexGhost
    (remaining start : ℕ) (hbound : start+remaining ≤ N) (v : Fin (remaining+1)) :
    HEq (markedMemoryHistoryVertexGhost hZ
      (markedMemoryFiniteTransitions_segment hZ d remaining start hbound) v)
        (d.ghost (start+v.val) (by omega)) := by
  induction remaining generalizing start with
  | zero =>
    have hv : v = 0 := Fin.eq_zero v
    subst v
    rfl
  | succ remaining ih =>
    refine Fin.cases ?_ (fun w => ?_) v
    · rfl
    · have hw : (w.succ : ℕ) = w.val+1 := rfl
      change HEq (markedMemoryHistoryVertexGhost hZ
        (markedMemoryHistoryTransport hZ (d.link start (by omega)).symm
          (markedMemoryFiniteTransitions_segment hZ d remaining (start+1) (by omega))) w) _
      exact (markedMemoryHistoryTransport_vertexGhost hZ _ _ w).trans
        ((ih (start+1) (by omega) w).trans
          (markedMemoryFiniteTransitions_ghost_congr hZ d _ _ (by omega) (by omega) (by omega)))

theorem markedMemoryFiniteTransitions_segment_vertexEdge
    (remaining start : ℕ) (hbound : start+remaining ≤ N) (v : Fin remaining) :
    HEq (markedMemoryHistoryVertexEdge hZ
      (markedMemoryFiniteTransitions_segment hZ d remaining start hbound) v)
        (d.edge (start+v.val) (by omega)) := by
  induction remaining generalizing start with
  | zero => exact Fin.elim0 v
  | succ remaining ih =>
    refine Fin.cases ?_ (fun w => ?_) v
    · rfl
    · have hw : (w.succ : ℕ) = w.val+1 := rfl
      change HEq (markedMemoryHistoryVertexEdge hZ
        (markedMemoryHistoryTransport hZ (d.link start (by omega)).symm
          (markedMemoryFiniteTransitions_segment hZ d remaining (start+1) (by omega))) w) _
      exact (markedMemoryHistoryTransport_vertexEdge hZ _ _ w).trans
        ((ih (start+1) (by omega) w).trans
          (markedMemoryFiniteTransitions_edge_congr hZ d _ _ (by omega) (by omega) (by omega)))

theorem markedMemoryFiniteTransitions_history_vertexState (v : Fin (N+1)) :
    markedMemoryHistoryVertexState hZ (markedMemoryFiniteTransitions_history hZ d) v =
      d.state v.val (by omega) := by
  simpa only [markedMemoryFiniteTransitions_history, Nat.zero_add] using
    markedMemoryFiniteTransitions_segment_vertexState hZ d N 0 (by omega) v

theorem markedMemoryFiniteTransitions_history_vertexGhost (v : Fin (N+1)) :
    HEq (markedMemoryHistoryVertexGhost hZ (markedMemoryFiniteTransitions_history hZ d) v)
      (d.ghost v.val (by omega)) := by
  exact (markedMemoryFiniteTransitions_segment_vertexGhost hZ d N 0 (by omega) v).trans
    (markedMemoryFiniteTransitions_ghost_congr hZ d (0+v.val) v.val (by omega) (by omega) (Nat.zero_add v.val))

theorem markedMemoryFiniteTransitions_history_vertexEdge (v : Fin N) :
    HEq (markedMemoryHistoryVertexEdge hZ (markedMemoryFiniteTransitions_history hZ d) v)
      (d.edge v.val (by omega)) := by
  exact (markedMemoryFiniteTransitions_segment_vertexEdge hZ d N 0 (by omega) v).trans
    (markedMemoryFiniteTransitions_edge_congr hZ d (0+v.val) v.val (by omega) (by omega) (Nat.zero_add v.val))

end
end ArtinMatthews
