module

public import ArtinMatthews.MarkedMemoryHistoryTraceBirths
public import ArtinMatthews.MarkedMemoryHistoryGhostDeaths
public import ArtinMatthews.MarkedMemoryHistoryEdgeSlotDeaths
public import ArtinMatthews.MarkedMemoryHistoryPresence


set_option backward.privateInPublic true
@[expose] public section

/-! Every actual trace birth is realized; the extension after the terminal
ghost is constant and creates no further particles. -/
namespace ArtinMatthews
noncomputable section

theorem markedMemoryHistoryTraceState_terminal {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) {t : ℕ} (ht : 2*n+1 ≤ t) :
    markedMemoryHistoryTraceState hZ history t = markedMemoryChronologicalTarget hZ history := by
  induction n generalizing s t with
  | zero =>
    cases t with
    | zero => omega
    | succ t => rfl
  | succ n ih =>
    cases t with
    | zero => omega
    | succ t =>
      cases t with
      | zero => omega
      | succ t => exact ih history.2.2 (by omega)

/-- The birth-time tag of every real performed birth lies before the final population. -/
theorem markedMemoryHistoryTraceBirth_time_lt {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (t : ℕ)
    (birth : MarkedMemoryHistoryTraceBirth hZ history t) : t < 2*n+1 := by
  induction n generalizing s t with
  | zero =>
    cases t with
    | zero => omega
    | succ t => exact PEmpty.elim birth
  | succ n ih =>
    cases t with
    | zero => omega
    | succ t =>
      cases t with
      | zero => omega
      | succ t => have h := ih history.2.2 t birth; omega

/-- Every actual performed birth has its unique next-population location. -/
theorem markedMemoryHistoryTraceStep_birth_range {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (t : ℕ)
    (birth : MarkedMemoryHistoryTraceBirth hZ history t) :
    ∃! i, markedMemoryHistoryTraceStep hZ history t i = Sum.inr birth := by
  induction n generalizing s t with
  | zero =>
    cases t with
    | zero => exact markedMemoryGhostOrigin_birth_range hZ s history birth
    | succ t => exact PEmpty.elim birth
  | succ n ih =>
    cases t with
    | zero => exact markedMemoryGhostOrigin_birth_range hZ s history.1 birth
    | succ t =>
      cases t with
      | zero => exact markedMemoryEdgeSlotOrigin_birth_range hZ _ history.2.1 birth
      | succ t => exact ih history.2.2 t birth

/-- Every actual performed birth is present at its actual birth time. -/
theorem markedMemoryHistoryTraceBirth_present {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (t : ℕ)
    (birth : MarkedMemoryHistoryTraceBirth hZ history t) :
    MarkedMemoryLineagePresent
      (T := fun t => MarkedMemoryPopulationIndex (markedMemoryHistoryTraceState hZ history t))
      (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history) (t+1) (Sum.inr ⟨t,birth⟩) := by
  obtain ⟨i,hi,_⟩ := markedMemoryHistoryTraceStep_birth_range hZ history t birth
  exact ⟨i,by simp only [markedMemoryLineageOrigin, hi, Sum.elim_inr]⟩

end
end ArtinMatthews
