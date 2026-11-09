module

public import ArtinMatthews.MarkedMemoryTransitionTrace


set_option backward.privateInPublic true
@[expose] public section

/-! Literal finite-time birth types of the assembled trace. Equalities
retain the actual dependent ghost/edge payload, not only its prime mark. -/
namespace ArtinMatthews
noncomputable section
variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)

theorem markedMemoryHistoryTransport_traceBirth {n : ℕ}
    {s t : MarkedRawState P (pads+1) B Z} (h : s = t)
    (history : MarkedMemoryChronologicalHistory hZ n s) (u : ℕ) :
    MarkedMemoryHistoryTraceBirth hZ (markedMemoryHistoryTransport hZ h history) u =
      MarkedMemoryHistoryTraceBirth hZ history u := by
  cases h
  rfl

variable {N : ℕ} (d : MarkedMemoryFiniteTransitions (P := P) (pads := pads) (B := B) hZ N)

theorem markedMemoryFiniteTransitions_ghostBirth_congr
    (a b : ℕ) (ha : a ≤ N) (hb : b ≤ N) (h : a = b) :
    MarkedMemoryGhostBirthIndex (d.ghost a ha) = MarkedMemoryGhostBirthIndex (d.ghost b hb) := by
  subst b
  rfl

theorem markedMemoryFiniteTransitions_edgeBirth_congr
    (a b : ℕ) (ha : a < N) (hb : b < N) (h : a = b) :
    MarkedMemoryEdgeBirthIndex (d.edge a ha) = MarkedMemoryEdgeBirthIndex (d.edge b hb) := by
  subst b
  rfl

theorem markedMemoryFiniteTransitions_segment_trace_ghostBirth
    (remaining start : ℕ) (hbound : start+remaining ≤ N) (r : ℕ) (hr : r ≤ remaining) :
    MarkedMemoryHistoryTraceBirth hZ
      (markedMemoryFiniteTransitions_segment hZ d remaining start hbound) (2*r) =
        MarkedMemoryGhostBirthIndex (d.ghost (start+r) (by omega)) := by
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
      change MarkedMemoryHistoryTraceBirth hZ
        (markedMemoryHistoryTransport hZ (d.link start (by omega)).symm
          (markedMemoryFiniteTransitions_segment hZ d remaining (start+1) (by omega))) (2*r) = _
      rw [markedMemoryHistoryTransport_traceBirth]
      exact (ih (start+1) (by omega) r (by omega)).trans
        (markedMemoryFiniteTransitions_ghostBirth_congr hZ d _ _ (by omega) (by omega) (by omega))

theorem markedMemoryFiniteTransitions_segment_trace_edgeBirth
    (remaining start : ℕ) (hbound : start+remaining ≤ N) (r : ℕ) (hr : r < remaining) :
    MarkedMemoryHistoryTraceBirth hZ
      (markedMemoryFiniteTransitions_segment hZ d remaining start hbound) (2*r+1) =
        MarkedMemoryEdgeBirthIndex (d.edge (start+r) (by omega)) := by
  induction remaining generalizing start r with
  | zero => omega
  | succ remaining ih =>
    cases r with
    | zero => rfl
    | succ r =>
      rw [show 2*(r+1)+1 = (2*r+1)+2 by omega]
      change MarkedMemoryHistoryTraceBirth hZ
        (markedMemoryHistoryTransport hZ (d.link start (by omega)).symm
          (markedMemoryFiniteTransitions_segment hZ d remaining (start+1) (by omega))) (2*r+1) = _
      rw [markedMemoryHistoryTransport_traceBirth]
      exact (ih (start+1) (by omega) r (by omega)).trans
        (markedMemoryFiniteTransitions_edgeBirth_congr hZ d _ _ (by omega) (by omega) (by omega))

theorem markedMemoryFiniteTransitions_history_trace_ghostBirth (r : ℕ) (hr : r ≤ N) :
    MarkedMemoryHistoryTraceBirth hZ (markedMemoryFiniteTransitions_history hZ d) (2*r) =
      MarkedMemoryGhostBirthIndex (d.ghost r hr) :=
  (markedMemoryFiniteTransitions_segment_trace_ghostBirth hZ d N 0 (by omega) r hr).trans
    (markedMemoryFiniteTransitions_ghostBirth_congr hZ d (0+r) r (by omega) hr (Nat.zero_add r))

theorem markedMemoryFiniteTransitions_history_trace_edgeBirth (r : ℕ) (hr : r < N) :
    MarkedMemoryHistoryTraceBirth hZ (markedMemoryFiniteTransitions_history hZ d) (2*r+1) =
      MarkedMemoryEdgeBirthIndex (d.edge r hr) :=
  (markedMemoryFiniteTransitions_segment_trace_edgeBirth hZ d N 0 (by omega) r hr).trans
    (markedMemoryFiniteTransitions_edgeBirth_congr hZ d (0+r) r (by omega) hr (Nat.zero_add r))

end
end ArtinMatthews
