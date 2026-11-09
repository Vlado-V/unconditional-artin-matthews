module

public import ArtinMatthews.MarkedMemoryHistoryGhostScalar
public import ArtinMatthews.MarkedMemoryHistoryRunWeight
public import ArtinMatthews.MarkedMemoryHistoryPrimewise


set_option backward.privateInPublic true
@[expose] public section

/-! Every literal ghost scalar is assigned to its actual trace identity.
The finite product is regrouped by these identities, without replacing
them by numeric primes or postulating a lifespan product identity. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)

def markedMemoryHistoryVertexGhost :
    {n : ℕ} → {s : MarkedRawState P (pads+1) B Z} →
      (history : MarkedMemoryChronologicalHistory hZ n s) → (v : Fin (n+1)) →
        MarkedMemoryGhostChoice hZ (markedMemoryHistoryVertexState hZ history v)
  | 0,_,ghost,_ => ghost
  | _+1,_,history,v => Fin.cases history.1
      (fun w => markedMemoryHistoryVertexGhost history.2.2 w) v

def markedMemoryHistoryGhostTime (n : ℕ) (v : Fin (n+1)) : ℕ :=
  markedMemoryHistoryStageTime (markedMemoryHistoryVertexStage n v)

theorem markedMemoryHistoryGhostTime_eq (n : ℕ) (v : Fin (n+1)) :
    markedMemoryHistoryGhostTime n v = 2*v.val := by
  induction n with
  | zero => have hv : v = 0 := Fin.eq_zero v; subst v; rfl
  | succ n ih =>
    refine Fin.cases ?_ (fun w => ?_) v
    · rfl
    · change markedMemoryHistoryGhostTime n w + 2 = 2*(w.val+1)
      rw [ih]
      omega

def markedMemoryHistoryGhostTraceBirth :
    {n : ℕ} → {s : MarkedRawState P (pads+1) B Z} →
      (history : MarkedMemoryChronologicalHistory hZ n s) → (v : Fin (n+1)) →
        MarkedMemoryGhostBirthIndex (markedMemoryHistoryVertexGhost hZ history v) →
          MarkedMemoryHistoryTraceBirth hZ history (markedMemoryHistoryGhostTime n v)
  | 0,_,_,_,b => b
  | _+1,_,history,v,b =>
      Fin.cases (fun b => b) (fun w b => markedMemoryHistoryGhostTraceBirth history.2.2 w b) v b

def markedMemoryHistoryGhostSourceIndex {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (v : Fin (n+1))
    (i : MarkedMemoryPopulationIndex (markedMemoryHistoryVertexState hZ history v)) :
    MarkedMemoryHistoryTracePopulation hZ history (markedMemoryHistoryGhostTime n v) :=
  cast (congrArg MarkedMemoryPopulationIndex
    (markedMemoryHistoryTraceState_stage hZ history (markedMemoryHistoryVertexStage n v))).symm i

def markedMemoryHistoryGhostSourceOrigin {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (v : Fin (n+1))
    (i : MarkedMemoryPopulationIndex (markedMemoryHistoryVertexState hZ history v)) :
    MarkedMemoryHistoryTraceAddress hZ history :=
  markedMemoryLineageOrigin (T := MarkedMemoryHistoryTracePopulation hZ history)
    (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history)
    (markedMemoryHistoryGhostTime n v) (markedMemoryHistoryGhostSourceIndex hZ history v i)

abbrev MarkedMemoryHistoryGhostScalarEvent {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) :=
  Σ v : Fin (n+1), MarkedMemoryGhostScalarEvent hZ (markedMemoryHistoryVertexState hZ history v)
    (markedMemoryHistoryVertexGhost hZ history v)

def markedMemoryHistoryGhostScalarOrigin {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s)
    (event : MarkedMemoryHistoryGhostScalarEvent hZ history) : MarkedMemoryHistoryTraceAddress hZ history :=
  match event.2 with
  | Sum.inl old => markedMemoryHistoryGhostSourceOrigin hZ history event.1 (Sum.inr old)
  | Sum.inr birth => Sum.inr ⟨markedMemoryHistoryGhostTime n event.1,
      markedMemoryHistoryGhostTraceBirth hZ history event.1 birth⟩

def markedMemoryHistoryGhostEventScalar {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (qStage : ℕ → ℝ) (j : ℕ)
    (event : MarkedMemoryHistoryGhostScalarEvent hZ history) : ℝ :=
  markedMemoryGhostEventScalar hZ (markedMemoryHistoryVertexState hZ history event.1)
    (markedMemoryHistoryVertexGhost hZ history event.1) (qStage (j+event.1.val)) event.2

def markedMemoryHistoryGhostScalarProduct {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (qStage : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∏ event : MarkedMemoryHistoryGhostScalarEvent hZ history,
    markedMemoryHistoryGhostEventScalar hZ history qStage j event

def markedMemoryHistoryBirthFactorials {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) : ℝ :=
  ∏ v : Fin (n+1), markedMemoryGhostBirthFactorial hZ (markedMemoryHistoryVertexState hZ history v)
    (markedMemoryHistoryVertexGhost hZ history v)

variable [DecidableEq J]

def markedMemoryHistoryLifespanScalar {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (qStage : ℕ → ℝ) (j : ℕ)
    (a : MarkedMemoryHistoryTraceAddress hZ history) : ℝ :=
  ∏ event : {event : MarkedMemoryHistoryGhostScalarEvent hZ history //
      markedMemoryHistoryGhostScalarOrigin hZ history event = a},
    markedMemoryHistoryGhostEventScalar hZ history qStage j event.1

/-- Exact finite scalar regrouping along the actual trace-origin map. -/
theorem markedMemoryHistoryGhostScalarProduct_lifespans {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (qStage : ℕ → ℝ) (j : ℕ) :
    markedMemoryHistoryGhostScalarProduct hZ history qStage j =
      ∏ a : MarkedMemoryHistoryTraceAddress hZ history,
        markedMemoryHistoryLifespanScalar hZ history qStage j a :=
  (Fintype.prod_fiberwise (markedMemoryHistoryGhostScalarOrigin hZ history)
    (markedMemoryHistoryGhostEventScalar hZ history qStage j)).symm

end
end ArtinMatthews
