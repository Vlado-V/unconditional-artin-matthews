module

public import ArtinMatthews.MarkedMemoryIndependentTraceValues
public import ArtinMatthews.MarkedMemoryIndependentTraceBirths
public import ArtinMatthews.MarkedMemoryIndependentEdgeLabelStep
public import ArtinMatthews.MarkedMemoryLabelTransport


set_option backward.privateInPublic true
@[expose] public section

/-! The actual finite trace of the reconstructed history preserves the
independent identity labels. Local ghost and slotted-edge equations are
transported through the proved trace-state and birth-type equalities. -/
namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j, DecidableEq (A j)] [∀ j, Fintype (A j)]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {n : ℕ}
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (order : Fin n → J → Equiv.Perm (Fin pads))

local notation "history" => markedMemoryIndependentHistory hZ d order

theorem markedMemoryIndependentTraceLabel_ghostStep (r : ℕ) (hr : r ≤ n)
    (x : MarkedMemoryPopulationIndex (markedMemoryHistoryTraceState hZ history (2*r+1))) :
    Sum.elim (markedMemoryIndependentTraceIds hZ d order (2*r) (by omega))
      (markedMemoryIndependentTraceBirthLabel hZ d order (2*r) (by omega))
      (markedMemoryHistoryTraceStep hZ history (2*r) x) =
        markedMemoryIndependentTraceIds hZ d order (2*r+1) (by omega) x := by
  let he := markedMemoryIndependentHistory_trace_even hZ d order r hr
  let hg := markedMemoryFiniteTransitions_history_trace_odd hZ (markedMemoryIndependentTransitions hZ d order) r hr
  let hb := markedMemoryIndependentTraceBirth_even hZ d order r hr
  have h := markedMemorySumLabel_transport (congrArg MarkedMemoryPopulationIndex hg)
    (congrArg MarkedMemoryPopulationIndex he) hb
    (markedMemoryHistoryTraceStep hZ history (2*r))
    (markedMemoryGhostPopulationOrigin hZ (markedMemoryIndependentState hZ d r hr) (markedMemoryIndependentGhost hZ d r hr))
    (markedMemoryIndependentHistory_trace_ghostOrigin hZ d order r hr)
    (markedMemoryIndependentVertexValue hZ d r hr) (markedMemoryIndependentGhostBirthLabel hZ d r hr)
    (fun i => markedMemoryIndependentPostGhostValue hZ d r hr
      (markedMemoryPopulationStateCast (markedMemoryIndependentGhost_target hZ d r hr) i))
    (markedMemoryIndependentGhost_label_step hZ d r hr) x
  have hs : (markedMemoryIndependentTraceIds hZ d order (2*r) (by omega) : _ → Σ j, A j) =
      fun y => markedMemoryIndependentVertexValue hZ d r hr (cast (congrArg MarkedMemoryPopulationIndex he) y) := by
    funext y
    exact markedMemoryIndependentTraceIds_even hZ d order r hr y
  have hn : markedMemoryIndependentTraceBirthLabel hZ d order (2*r) (by omega) =
      fun b => markedMemoryIndependentGhostBirthLabel hZ d r hr (cast hb b) := by
    funext b
    exact markedMemoryIndependentTraceBirthLabel_even hZ d order r hr b
  have ht := congrArg (markedMemoryIndependentPostGhostValue hZ d r hr)
    (markedMemoryPopulationStateCast_trans hg (markedMemoryIndependentGhost_target hZ d r hr) x)
  exact (congrArg₂ (fun a b => Sum.elim a b (markedMemoryHistoryTraceStep hZ history (2*r) x)) hs hn).trans
    (h.trans (ht.trans (markedMemoryIndependentTraceIds_odd hZ d order r hr x).symm))

theorem markedMemoryIndependentTraceLabel_edgeStep (r : ℕ) (hr : r < n)
    (x : MarkedMemoryPopulationIndex (markedMemoryHistoryTraceState hZ history ((2*r+1)+1))) :
    Sum.elim (markedMemoryIndependentTraceIds hZ d order (2*r+1) (by omega))
      (markedMemoryIndependentTraceBirthLabel hZ d order (2*r+1) (by omega))
      (markedMemoryHistoryTraceStep hZ history (2*r+1) x) =
        markedMemoryIndependentTraceIds hZ d order ((2*r+1)+1) (by omega) x := by
  have htime : (2*r+1)+1 = 2*(r+1) := by omega
  let he := (congrArg (markedMemoryHistoryTraceState hZ history) htime).trans
    (markedMemoryIndependentHistory_trace_even hZ d order (r+1) hr)
  let hs := markedMemoryIndependentHistory_trace_odd hZ d order r (Nat.le_of_lt hr)
  let hb := markedMemoryIndependentTraceBirth_odd hZ d order r hr
  let et := markedMemoryIndependentEdge_target hZ d r hr (order ⟨r,hr⟩)
  have h := markedMemorySumLabel_transport (congrArg MarkedMemoryPopulationIndex (he.trans et.symm))
    (congrArg MarkedMemoryPopulationIndex hs) hb
    (markedMemoryHistoryTraceStep hZ history (2*r+1))
    (markedMemoryEdgeSlotPopulationOrigin hZ (markedMemoryIndependentPostGhost hZ d r (Nat.le_of_lt hr))
      (markedMemoryIndependentEdge hZ d r hr (order ⟨r,hr⟩)))
    (markedMemoryIndependentHistory_trace_edgeOrigin hZ d order r hr)
    (markedMemoryIndependentPostGhostValue hZ d r (Nat.le_of_lt hr))
    (markedMemoryIndependentEdgeBirthLabel hZ d r hr (order ⟨r,hr⟩))
    (fun i => markedMemoryIndependentVertexValue hZ d (r+1) hr (markedMemoryPopulationStateCast et i))
    (markedMemoryIndependentEdge_label_step hZ d r hr (order ⟨r,hr⟩)) x
  have hsrc : (markedMemoryIndependentTraceIds hZ d order (2*r+1) (by omega) : _ → Σ j, A j) =
      fun y => markedMemoryIndependentPostGhostValue hZ d r (Nat.le_of_lt hr) (cast (congrArg MarkedMemoryPopulationIndex hs) y) := by
    funext y
    exact markedMemoryIndependentTraceIds_odd hZ d order r (Nat.le_of_lt hr) y
  have hn : markedMemoryIndependentTraceBirthLabel hZ d order (2*r+1) (by omega) =
      fun b => markedMemoryIndependentEdgeBirthLabel hZ d r hr (order ⟨r,hr⟩) (cast hb b) := by
    funext b
    exact markedMemoryIndependentTraceBirthLabel_odd hZ d order r hr b
  have ht := congrArg (markedMemoryIndependentVertexValue hZ d (r+1) hr)
    (markedMemoryPopulationStateCast_trans (he.trans et.symm) et x)
  exact (congrArg₂ (fun a b => Sum.elim a b (markedMemoryHistoryTraceStep hZ history (2*r+1) x)) hsrc hn).trans
    (h.trans (ht.trans (markedMemoryIndependentTraceIds_even_at hZ d order _ (r+1) (by omega) hr htime x).symm))

theorem markedMemoryIndependentTraceLabel_step (t : ℕ) (ht : t < 2*n+1)
    (x : MarkedMemoryPopulationIndex (markedMemoryHistoryTraceState hZ history (t+1))) :
    Sum.elim (markedMemoryIndependentTraceIds hZ d order t (Nat.le_of_lt ht))
      (markedMemoryIndependentTraceBirthLabel hZ d order t ht)
      (markedMemoryHistoryTraceStep hZ history t x) =
        markedMemoryIndependentTraceIds hZ d order (t+1) ht x := by
  by_cases he : t % 2 = 0
  · obtain ⟨r,rfl⟩ : ∃ r, t = 2*r := ⟨t/2,by omega⟩
    exact markedMemoryIndependentTraceLabel_ghostStep hZ d order r (by omega) x
  · obtain ⟨r,rfl⟩ : ∃ r, t = 2*r+1 := ⟨t/2,by omega⟩
    exact markedMemoryIndependentTraceLabel_edgeStep hZ d order r (by omega) x

end
end ArtinMatthews
