module

public import ArtinMatthews.MarkedMemoryTransitionAssembly
public import ArtinMatthews.MarkedMemoryHistoryTrace


set_option backward.privateInPublic true
@[expose] public section

/-! The deterministic local-transition assembler has exactly its prescribed
states and indexed old/new lineage maps at every ghost and edge time. -/
namespace ArtinMatthews
noncomputable section
variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)

theorem markedMemoryHistoryTransport_traceState {n : ℕ}
    {s t : MarkedRawState P (pads+1) B Z} (h : s = t)
    (history : MarkedMemoryChronologicalHistory hZ n s) (u : ℕ) :
    markedMemoryHistoryTraceState hZ (markedMemoryHistoryTransport hZ h history) u =
      markedMemoryHistoryTraceState hZ history u := by
  cases h
  rfl

theorem markedMemoryHistoryTransport_traceStep {n : ℕ}
    {s t : MarkedRawState P (pads+1) B Z} (h : s = t)
    (history : MarkedMemoryChronologicalHistory hZ n s) (u : ℕ) :
    HEq (markedMemoryHistoryTraceStep hZ (markedMemoryHistoryTransport hZ h history) u)
      (markedMemoryHistoryTraceStep hZ history u) := by
  cases h
  rfl

variable {N : ℕ} (d : MarkedMemoryFiniteTransitions (P := P) (pads := pads) (B := B) hZ N)

theorem markedMemoryFiniteTransitions_state_congr
    (a b : ℕ) (ha : a ≤ N) (hb : b ≤ N) (h : a = b) : d.state a ha = d.state b hb := by
  subst b
  rfl

theorem markedMemoryFiniteTransitions_ghostOrigin_congr
    (a b : ℕ) (ha : a ≤ N) (hb : b ≤ N) (h : a = b) :
    HEq (markedMemoryGhostPopulationOrigin hZ (d.state a ha) (d.ghost a ha))
      (markedMemoryGhostPopulationOrigin hZ (d.state b hb) (d.ghost b hb)) := by
  subst b
  rfl

theorem markedMemoryFiniteTransitions_edgeOrigin_congr
    (a b : ℕ) (ha : a < N) (hb : b < N) (h : a = b) :
    HEq (markedMemoryEdgeSlotPopulationOrigin hZ
      (markedMemoryGhostChoiceTarget hZ (d.state a (Nat.le_of_lt ha))
        (d.ghost a (Nat.le_of_lt ha))) (d.edge a ha))
      (markedMemoryEdgeSlotPopulationOrigin hZ
        (markedMemoryGhostChoiceTarget hZ (d.state b (Nat.le_of_lt hb))
          (d.ghost b (Nat.le_of_lt hb))) (d.edge b hb)) := by
  subst b
  rfl

theorem markedMemoryFiniteTransitions_segment_trace_even
    (remaining start : ℕ) (hbound : start+remaining ≤ N) (r : ℕ) (hr : r ≤ remaining) :
    markedMemoryHistoryTraceState hZ
      (markedMemoryFiniteTransitions_segment hZ d remaining start hbound) (2*r) =
        d.state (start+r) (by omega) := by
  induction remaining generalizing start r with
  | zero =>
    have hr0 : r = 0 := by omega
    subst r
    rfl
  | succ remaining ih =>
    cases r with
    | zero => rfl
    | succ r =>
      rw [show 2*(r+1) = 2*r+2 by omega]
      change markedMemoryHistoryTraceState hZ
        (markedMemoryHistoryTransport hZ (d.link start (by omega)).symm
          (markedMemoryFiniteTransitions_segment hZ d remaining (start+1) (by omega))) (2*r) = _
      rw [markedMemoryHistoryTransport_traceState]
      exact (ih (start+1) (by omega) r (by omega)).trans
        (markedMemoryFiniteTransitions_state_congr hZ d _ _ (by omega) (by omega) (by omega))

theorem markedMemoryFiniteTransitions_segment_trace_odd
    (remaining start : ℕ) (hbound : start+remaining ≤ N) (r : ℕ) (hr : r ≤ remaining) :
    markedMemoryHistoryTraceState hZ
      (markedMemoryFiniteTransitions_segment hZ d remaining start hbound) (2*r+1) =
        markedMemoryGhostChoiceTarget hZ (d.state (start+r) (by omega))
          (d.ghost (start+r) (by omega)) := by
  induction remaining generalizing start r with
  | zero =>
    have hr0 : r = 0 := by omega
    subst r
    rfl
  | succ remaining ih =>
    cases r with
    | zero => rfl
    | succ r =>
      rw [show 2*(r+1)+1 = (2*r+1)+2 by omega]
      change markedMemoryHistoryTraceState hZ
        (markedMemoryHistoryTransport hZ (d.link start (by omega)).symm
          (markedMemoryFiniteTransitions_segment hZ d remaining (start+1) (by omega))) (2*r+1) = _
      rw [markedMemoryHistoryTransport_traceState]
      exact (ih (start+1) (by omega) r (by omega)).trans
        (markedMemoryFiniteTransitions_ghostTarget_congr hZ d _ _ (by omega) (by omega) (by omega))

theorem markedMemoryFiniteTransitions_segment_trace_ghostStep
    (remaining start : ℕ) (hbound : start+remaining ≤ N) (r : ℕ) (hr : r ≤ remaining) :
    HEq (markedMemoryHistoryTraceStep hZ
      (markedMemoryFiniteTransitions_segment hZ d remaining start hbound) (2*r))
      (markedMemoryGhostPopulationOrigin hZ (d.state (start+r) (by omega))
        (d.ghost (start+r) (by omega))) := by
  induction remaining generalizing start r with
  | zero =>
    have hr0 : r = 0 := by omega
    subst r
    rfl
  | succ remaining ih =>
    cases r with
    | zero => rfl
    | succ r =>
      rw [show 2*(r+1) = 2*r+2 by omega]
      change HEq (markedMemoryHistoryTraceStep hZ
        (markedMemoryHistoryTransport hZ (d.link start (by omega)).symm
          (markedMemoryFiniteTransitions_segment hZ d remaining (start+1) (by omega))) (2*r)) _
      exact (markedMemoryHistoryTransport_traceStep hZ _ _ _).trans
        ((ih (start+1) (by omega) r (by omega)).trans
          (markedMemoryFiniteTransitions_ghostOrigin_congr hZ d _ _ (by omega) (by omega) (by omega)))

theorem markedMemoryFiniteTransitions_segment_trace_edgeStep
    (remaining start : ℕ) (hbound : start+remaining ≤ N) (r : ℕ) (hr : r < remaining) :
    HEq (markedMemoryHistoryTraceStep hZ
      (markedMemoryFiniteTransitions_segment hZ d remaining start hbound) (2*r+1))
      (markedMemoryEdgeSlotPopulationOrigin hZ
        (markedMemoryGhostChoiceTarget hZ (d.state (start+r) (by omega))
          (d.ghost (start+r) (by omega))) (d.edge (start+r) (by omega))) := by
  induction remaining generalizing start r with
  | zero => omega
  | succ remaining ih =>
    cases r with
    | zero => rfl
    | succ r =>
      rw [show 2*(r+1)+1 = (2*r+1)+2 by omega]
      change HEq (markedMemoryHistoryTraceStep hZ
        (markedMemoryHistoryTransport hZ (d.link start (by omega)).symm
          (markedMemoryFiniteTransitions_segment hZ d remaining (start+1) (by omega))) (2*r+1)) _
      exact (markedMemoryHistoryTransport_traceStep hZ _ _ _).trans
        ((ih (start+1) (by omega) r (by omega)).trans
          (markedMemoryFiniteTransitions_edgeOrigin_congr hZ d _ _ (by omega) (by omega) (by omega)))

theorem markedMemoryFiniteTransitions_history_trace_even (r : ℕ) (hr : r ≤ N) :
    markedMemoryHistoryTraceState hZ (markedMemoryFiniteTransitions_history hZ d) (2*r) =
      d.state r hr := by
  simpa only [markedMemoryFiniteTransitions_history, Nat.zero_add] using
    markedMemoryFiniteTransitions_segment_trace_even hZ d N 0 (by omega) r hr

theorem markedMemoryFiniteTransitions_history_trace_odd (r : ℕ) (hr : r ≤ N) :
    markedMemoryHistoryTraceState hZ (markedMemoryFiniteTransitions_history hZ d) (2*r+1) =
      markedMemoryGhostChoiceTarget hZ (d.state r hr) (d.ghost r hr) := by
  exact (markedMemoryFiniteTransitions_segment_trace_odd hZ d N 0 (by omega) r hr).trans
    (markedMemoryFiniteTransitions_ghostTarget_congr hZ d (0+r) r (by omega) hr (Nat.zero_add r))

theorem markedMemoryFiniteTransitions_history_trace_ghostStep (r : ℕ) (hr : r ≤ N) :
    HEq (markedMemoryHistoryTraceStep hZ (markedMemoryFiniteTransitions_history hZ d) (2*r))
      (markedMemoryGhostPopulationOrigin hZ (d.state r hr) (d.ghost r hr)) := by
  have htrace := markedMemoryFiniteTransitions_segment_trace_ghostStep hZ d N 0 (by omega) r hr
  have hindex := markedMemoryFiniteTransitions_ghostOrigin_congr hZ d (0+r) r (by omega) hr (Nat.zero_add r)
  exact htrace.trans hindex

theorem markedMemoryFiniteTransitions_history_trace_edgeStep (r : ℕ) (hr : r < N) :
    HEq (markedMemoryHistoryTraceStep hZ (markedMemoryFiniteTransitions_history hZ d) (2*r+1))
      (markedMemoryEdgeSlotPopulationOrigin hZ
        (markedMemoryGhostChoiceTarget hZ (d.state r (Nat.le_of_lt hr))
          (d.ghost r (Nat.le_of_lt hr))) (d.edge r hr)) := by
  have htrace := markedMemoryFiniteTransitions_segment_trace_edgeStep hZ d N 0 (by omega) r hr
  have hindex := markedMemoryFiniteTransitions_edgeOrigin_congr hZ d (0+r) r (by omega) hr (Nat.zero_add r)
  exact htrace.trans hindex

end
end ArtinMatthews
