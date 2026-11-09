module

public import ArtinMatthews.MarkedMemoryIndependentTraceState
public import ArtinMatthews.MarkedMemoryIndependentBirths
public import ArtinMatthews.MarkedMemoryTransitionBirthTrace
public import ArtinMatthews.MarkedMemoryLabelTransport


set_option backward.privateInPublic true
@[expose] public section

/-! Actual finite trace births are labeled by the independently
constructed ghost batch or fresh incoming identity. Their first times
are derived from the independent interval laws. -/
namespace ArtinMatthews
noncomputable section
universe u v

variable {J : Type u} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)

theorem markedMemoryEdgeTransport_birthType {s t : MarkedRawState P (pads+1) B Z}
    (h : s = t) (edge : MarkedMemoryEdgeChoice hZ s) :
    MarkedMemoryEdgeBirthIndex (markedMemoryEdgeTransport hZ h edge) = MarkedMemoryEdgeBirthIndex edge := by
  cases h
  rfl

variable {A : J → Type v} [∀ j, DecidableEq (A j)] [∀ j, Fintype (A j)] {n : ℕ}
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (order : Fin n → J → Equiv.Perm (Fin pads))

theorem markedMemoryIndependentTraceBirth_even (r : ℕ) (hr : r ≤ n) :
    MarkedMemoryHistoryTraceBirth hZ (markedMemoryIndependentHistory hZ d order) (2*r) =
      MarkedMemoryGhostBirthIndex (markedMemoryIndependentGhost hZ d r hr) :=
  markedMemoryFiniteTransitions_history_trace_ghostBirth hZ (markedMemoryIndependentTransitions hZ d order) r hr

theorem markedMemoryIndependentTraceBirth_odd (r : ℕ) (hr : r < n) :
    MarkedMemoryHistoryTraceBirth hZ (markedMemoryIndependentHistory hZ d order) (2*r+1) =
      MarkedMemoryEdgeBirthIndex (markedMemoryIndependentEdge hZ d r hr (order ⟨r,hr⟩)) :=
  (markedMemoryFiniteTransitions_history_trace_edgeBirth hZ (markedMemoryIndependentTransitions hZ d order) r hr).trans
    (markedMemoryEdgeTransport_birthType hZ (markedMemoryIndependentGhost_target hZ d r (Nat.le_of_lt hr)).symm
      (markedMemoryIndependentEdge hZ d r hr (order ⟨r,hr⟩)))

def markedMemoryIndependentTraceGhostLabel (t : ℕ) (ht : t < 2*n+1) (he : t % 2 = 0) :
    MarkedMemoryHistoryTraceBirth hZ (markedMemoryIndependentHistory hZ d order) t → Σ j, A j :=
  let hr : t/2 ≤ n := by omega
  let htime : t = 2*(t/2) := by omega
  let E : MarkedMemoryHistoryTraceBirth hZ (markedMemoryIndependentHistory hZ d order) t =
      MarkedMemoryGhostBirthIndex (markedMemoryIndependentGhost hZ d (t/2) hr) :=
    (congrArg (MarkedMemoryHistoryTraceBirth hZ (markedMemoryIndependentHistory hZ d order)) htime).trans
      (markedMemoryIndependentTraceBirth_even hZ d order (t/2) hr)
  fun b => markedMemoryIndependentGhostBirthLabel hZ d (t/2) hr (cast E b)

def markedMemoryIndependentTraceEdgeLabel (t : ℕ) (ht : t < 2*n+1) (he : ¬ t % 2 = 0) :
    MarkedMemoryHistoryTraceBirth hZ (markedMemoryIndependentHistory hZ d order) t → Σ j, A j :=
  let hr : t/2 < n := by omega
  let htime : t = 2*(t/2)+1 := by omega
  let E : MarkedMemoryHistoryTraceBirth hZ (markedMemoryIndependentHistory hZ d order) t =
      MarkedMemoryEdgeBirthIndex (markedMemoryIndependentEdge hZ d (t/2) hr (order ⟨t/2,hr⟩)) :=
    (congrArg (MarkedMemoryHistoryTraceBirth hZ (markedMemoryIndependentHistory hZ d order)) htime).trans
      (markedMemoryIndependentTraceBirth_odd hZ d order (t/2) hr)
  fun b => markedMemoryIndependentEdgeBirthLabel hZ d (t/2) hr (order ⟨t/2,hr⟩) (cast E b)

def markedMemoryIndependentTraceBirthLabel (t : ℕ) (ht : t < 2*n+1) :
    MarkedMemoryHistoryTraceBirth hZ (markedMemoryIndependentHistory hZ d order) t → Σ j, A j :=
  if he : t % 2 = 0 then markedMemoryIndependentTraceGhostLabel hZ d order t ht he
  else markedMemoryIndependentTraceEdgeLabel hZ d order t ht he

theorem markedMemoryIndependentGhostBirth_cast {X : Type u} (a b : ℕ) (ha : a ≤ n) (hb : b ≤ n) (h : a = b)
    (ea : X = MarkedMemoryGhostBirthIndex (markedMemoryIndependentGhost hZ d a ha))
    (eb : X = MarkedMemoryGhostBirthIndex (markedMemoryIndependentGhost hZ d b hb)) (x : X) :
    markedMemoryIndependentGhostBirthLabel hZ d a ha (cast ea x) =
      markedMemoryIndependentGhostBirthLabel hZ d b hb (cast eb x) := by
  subst b
  rfl

theorem markedMemoryIndependentEdgeBirth_cast {X : Type u} (a b : ℕ) (ha : a < n) (hb : b < n) (h : a = b)
    (ea : X = MarkedMemoryEdgeBirthIndex (markedMemoryIndependentEdge hZ d a ha (order ⟨a,ha⟩)))
    (eb : X = MarkedMemoryEdgeBirthIndex (markedMemoryIndependentEdge hZ d b hb (order ⟨b,hb⟩))) (x : X) :
    markedMemoryIndependentEdgeBirthLabel hZ d a ha (order ⟨a,ha⟩) (cast ea x) =
      markedMemoryIndependentEdgeBirthLabel hZ d b hb (order ⟨b,hb⟩) (cast eb x) := by
  subst b
  rfl

theorem markedMemoryIndependentTraceBirthLabel_of_even (t : ℕ) (ht : t < 2*n+1) (he : t % 2 = 0) :
    markedMemoryIndependentTraceBirthLabel hZ d order t ht = markedMemoryIndependentTraceGhostLabel hZ d order t ht he := by
  unfold markedMemoryIndependentTraceBirthLabel
  exact dite_eq_left he

theorem markedMemoryIndependentTraceBirthLabel_of_odd (t : ℕ) (ht : t < 2*n+1) (he : ¬ t % 2 = 0) :
    markedMemoryIndependentTraceBirthLabel hZ d order t ht = markedMemoryIndependentTraceEdgeLabel hZ d order t ht he := by
  unfold markedMemoryIndependentTraceBirthLabel
  exact dite_eq_right he

theorem markedMemoryIndependentTraceBirthLabel_first (t : ℕ) (ht : t < 2*n+1)
    (b : MarkedMemoryHistoryTraceBirth hZ (markedMemoryIndependentHistory hZ d order) t) :
    (d.lifespan (markedMemoryIndependentTraceBirthLabel hZ d order t ht b).1).first
      (markedMemoryIndependentTraceBirthLabel hZ d order t ht b).2 = t+1 := by
  by_cases he : t % 2 = 0
  · have hc := congrArg (fun f : MarkedMemoryHistoryTraceBirth hZ (markedMemoryIndependentHistory hZ d order) t → Σ j, A j =>
        (d.lifespan (f b).1).first (f b).2) (markedMemoryIndependentTraceBirthLabel_of_even hZ d order t ht he)
    have hr : t/2 ≤ n := by omega
    have htime : t = 2*(t/2) := by omega
    let E := (congrArg (MarkedMemoryHistoryTraceBirth hZ (markedMemoryIndependentHistory hZ d order)) htime).trans
      (markedMemoryIndependentTraceBirth_even hZ d order (t/2) hr)
    have hn : 2*(t/2)+1 = t+1 := by omega
    exact hc.trans ((markedMemoryIndependentGhostBirth_first hZ d (t/2) hr (cast E b)).trans hn)
  · have hc := congrArg (fun f : MarkedMemoryHistoryTraceBirth hZ (markedMemoryIndependentHistory hZ d order) t → Σ j, A j =>
        (d.lifespan (f b).1).first (f b).2) (markedMemoryIndependentTraceBirthLabel_of_odd hZ d order t ht he)
    have hr : t/2 < n := by omega
    have htime : t = 2*(t/2)+1 := by omega
    let E := (congrArg (MarkedMemoryHistoryTraceBirth hZ (markedMemoryIndependentHistory hZ d order)) htime).trans
      (markedMemoryIndependentTraceBirth_odd hZ d order (t/2) hr)
    have hn : (2*(t/2)+1)+1 = t+1 := by omega
    exact hc.trans ((markedMemoryIndependentEdgeBirth_first hZ d (t/2) hr (order ⟨t/2,hr⟩) (cast E b)).trans hn)

theorem markedMemoryIndependentTraceBirthLabel_even (r : ℕ) (hr : r ≤ n)
    (b : MarkedMemoryHistoryTraceBirth hZ (markedMemoryIndependentHistory hZ d order) (2*r)) :
    markedMemoryIndependentTraceBirthLabel hZ d order (2*r) (by omega) b =
      markedMemoryIndependentGhostBirthLabel hZ d r hr (cast (markedMemoryIndependentTraceBirth_even hZ d order r hr) b) := by
  have he : (2*r) % 2 = 0 := by omega
  have hd : (2*r)/2 = r := by omega
  exact (congrFun (markedMemoryIndependentTraceBirthLabel_of_even hZ d order (2*r) (by omega) he) b).trans
    (markedMemoryIndependentGhostBirth_cast hZ d ((2*r)/2) r (by omega) hr hd _ _ b)

theorem markedMemoryIndependentTraceBirthLabel_odd (r : ℕ) (hr : r < n)
    (b : MarkedMemoryHistoryTraceBirth hZ (markedMemoryIndependentHistory hZ d order) (2*r+1)) :
    markedMemoryIndependentTraceBirthLabel hZ d order (2*r+1) (by omega) b =
      markedMemoryIndependentEdgeBirthLabel hZ d r hr (order ⟨r,hr⟩)
        (cast (markedMemoryIndependentTraceBirth_odd hZ d order r hr) b) := by
  have he : ¬ (2*r+1) % 2 = 0 := by omega
  have hd : (2*r+1)/2 = r := by omega
  exact (congrFun (markedMemoryIndependentTraceBirthLabel_of_odd hZ d order (2*r+1) (by omega) he) b).trans
    (markedMemoryIndependentEdgeBirth_cast hZ d order ((2*r+1)/2) r (by omega) hr hd _ _ b)

end
end ArtinMatthews
