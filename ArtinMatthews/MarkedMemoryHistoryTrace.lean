module

public import ArtinMatthews.MarkedMemoryHistoryStages


set_option backward.privateInPublic true
@[expose] public section

/-! The actual chronological history as a total natural-time transition
trace. After its final ghost it is constant, with no additional births. -/
namespace ArtinMatthews
noncomputable section

def markedMemoryHistoryTraceStateAux {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) :
    ℕ → {n : ℕ} → {s : MarkedRawState P (pads+1) B Z} →
      MarkedMemoryChronologicalHistory hZ n s → MarkedRawState P (pads+1) B Z
  | 0,_,s,_ => s
  | _+1,0,s,ghost => markedMemoryGhostChoiceTarget hZ s ghost
  | 1,_+1,s,history => markedMemoryGhostChoiceTarget hZ s history.1
  | t+2,_+1,_,history => markedMemoryHistoryTraceStateAux hZ t history.2.2

abbrev markedMemoryHistoryTraceState {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (t : ℕ) : MarkedRawState P (pads+1) B Z :=
  markedMemoryHistoryTraceStateAux hZ t history

def MarkedMemoryHistoryTraceBirth {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) :
    {n : ℕ} → {s : MarkedRawState P (pads+1) B Z} →
      MarkedMemoryChronologicalHistory hZ n s → ℕ → Type _
  | 0,_,ghost,0 => MarkedMemoryGhostBirthIndex ghost
  | 0,_,_,_+1 => PEmpty
  | _+1,_,history,0 => MarkedMemoryGhostBirthIndex history.1
  | _+1,_,history,1 => MarkedMemoryEdgeBirthIndex history.2.1
  | _+1,_,history,t+2 => MarkedMemoryHistoryTraceBirth hZ history.2.2 t

def markedMemoryHistoryTraceBirthPrime {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) :
    {n : ℕ} → {s : MarkedRawState P (pads+1) B Z} →
      (history : MarkedMemoryChronologicalHistory hZ n s) → (t : ℕ) →
      MarkedMemoryHistoryTraceBirth hZ history t → Nat.Primes
  | 0,_,ghost,0 => markedMemoryGhostBirthPrime ghost
  | 0,_,_,_+1 => PEmpty.elim
  | _+1,_,history,0 => markedMemoryGhostBirthPrime history.1
  | _+1,_,history,1 => markedMemoryEdgeBirthPrime history.2.1
  | _+1,_,history,t+2 => markedMemoryHistoryTraceBirthPrime hZ history.2.2 t

/-- Every trace step is the actual old-or-performed-new indexed injection. -/
def markedMemoryHistoryTraceStep {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) :
    {n : ℕ} → {s : MarkedRawState P (pads+1) B Z} →
      (history : MarkedMemoryChronologicalHistory hZ n s) → (t : ℕ) →
      MarkedMemoryPopulationIndex (markedMemoryHistoryTraceState hZ history (t+1)) ↪
        (MarkedMemoryPopulationIndex (markedMemoryHistoryTraceState hZ history t) ⊕
          MarkedMemoryHistoryTraceBirth hZ history t)
  | 0,s,ghost,0 => markedMemoryGhostPopulationOrigin hZ s ghost
  | 0,_,_,_+1 => Function.Embedding.inl
  | _+1,s,history,0 => markedMemoryGhostPopulationOrigin hZ s history.1
  | _+1,s,history,1 => markedMemoryEdgeSlotPopulationOrigin hZ
      (markedMemoryGhostChoiceTarget hZ s history.1) history.2.1
  | _+1,_,history,t+2 => markedMemoryHistoryTraceStep hZ history.2.2 t

/-- The total trace agrees with the actual finite stage population. -/
theorem markedMemoryHistoryTraceState_stage {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (t : MarkedMemoryHistoryStage n) :
    markedMemoryHistoryTraceState hZ history (markedMemoryHistoryStageTime t) =
      markedMemoryHistoryStageState hZ history t := by
  induction n generalizing s with
  | zero => cases t <;> rfl
  | succ n ih =>
    rcases t with before | after | tail
    · rfl
    · rfl
    · exact ih history.2.2 tail

/-- No actual trace step changes the prime attached to an identity. -/
theorem markedMemoryHistoryTraceStep_prime {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (t : ℕ)
    (i : MarkedMemoryPopulationIndex (markedMemoryHistoryTraceState hZ history (t+1))) :
    Sum.elim (markedMemoryPopulationPrime (markedMemoryHistoryTraceState hZ history t))
      (markedMemoryHistoryTraceBirthPrime hZ history t) (markedMemoryHistoryTraceStep hZ history t i) =
        markedMemoryPopulationPrime (markedMemoryHistoryTraceState hZ history (t+1)) i := by
  induction n generalizing s t with
  | zero =>
    cases t with
    | zero => exact markedMemoryGhostPopulationOrigin_prime hZ s history i
    | succ t => rfl
  | succ n ih =>
    cases t with
    | zero => exact markedMemoryGhostPopulationOrigin_prime hZ s history.1 i
    | succ t =>
      cases t with
      | zero => exact markedMemoryEdgeSlotPopulationOrigin_prime hZ _ history.2.1 i
      | succ t => exact ih history.2.2 t i

end
end ArtinMatthews
