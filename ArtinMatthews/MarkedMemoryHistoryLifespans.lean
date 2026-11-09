module

public import ArtinMatthews.MarkedMemoryHistoryTraceComplete
public import ArtinMatthews.MarkedMemoryHistoryActualPresence


set_option backward.privateInPublic true
@[expose] public section

/-! The finite family of actual indexed lifespans, computed from every
initial particle and every performed birth. This does not yet identify the
signed history sum with the independent-line expansion. -/
namespace ArtinMatthews
noncomputable section

@[instance_reducible]
def markedMemoryHistoryBirths_fintype {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) :
    {n : ℕ} → {s : MarkedRawState P (pads+1) B Z} →
      (history : MarkedMemoryChronologicalHistory hZ n s) → Fintype (MarkedMemoryHistoryBirths hZ history)
  | 0,_,ghost => inferInstanceAs (Fintype (MarkedMemoryGhostBirthIndex ghost))
  | _+1,_,history => by
      letI := markedMemoryHistoryBirths_fintype hZ history.2.2
      change Fintype (MarkedMemoryGhostBirthIndex history.1 ⊕
        (MarkedMemoryEdgeBirthIndex history.2.1 ⊕ MarkedMemoryHistoryBirths hZ history.2.2))
      infer_instance

attribute [instance] markedMemoryHistoryBirths_fintype

/-- Every identity in the actual finite birth family really occurs. -/
theorem markedMemoryHistoryTraceAddress_present {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (a : MarkedMemoryHistoryTraceAddress hZ history) :
    ∃ t ≤ 2*n+1, MarkedMemoryLineagePresent
      (T := MarkedMemoryHistoryTracePopulation hZ history) (Birth := MarkedMemoryHistoryTraceBirth hZ history)
      (markedMemoryHistoryTraceStep hZ history) t a := by
  rcases a with old | ⟨t,birth⟩
  · exact ⟨0,Nat.zero_le _,old,rfl⟩
  · exact ⟨t+1,markedMemoryHistoryTraceBirth_time_lt hZ history t birth,
      markedMemoryHistoryTraceBirth_present hZ history t birth⟩

def markedMemoryHistoryLifespanLast {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (a : MarkedMemoryHistoryTraceAddress hZ history) : ℕ :=
  markedMemoryLineageLastPresent (T := MarkedMemoryHistoryTracePopulation hZ history)
    (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history) (2*n+1) a
    ((markedMemoryLineagePresenceTimes_nonempty_iff _ _ _).mpr
      (markedMemoryHistoryTraceAddress_present hZ history a))

/-- Every actual indexed lifespan is a genuine closed interval of the
chronological populations; this is derived without numeric distinctness. -/
theorem markedMemoryHistory_lifespan_exact {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (a : MarkedMemoryHistoryTraceAddress hZ history) (t : ℕ) :
    (t ≤ 2*n+1 ∧ MarkedMemoryLineagePresent
      (T := MarkedMemoryHistoryTracePopulation hZ history) (Birth := MarkedMemoryHistoryTraceBirth hZ history)
      (markedMemoryHistoryTraceStep hZ history) t a) ↔
        markedMemoryLineageBirthTime a ≤ t ∧ t ≤ markedMemoryHistoryLifespanLast hZ history a := by
  rw [← markedMemoryLineagePresenceTimes_mem]
  exact markedMemoryLineagePresenceTimes_mem_iff_between _ _ _ _ t

/-- The computed endpoint is inside the actual history horizon. -/
theorem markedMemoryHistory_lifespan_bounds {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (a : MarkedMemoryHistoryTraceAddress hZ history) :
    markedMemoryLineageBirthTime a ≤ markedMemoryHistoryLifespanLast hZ history a ∧
      markedMemoryHistoryLifespanLast hZ history a ≤ 2*n+1 := by
  have hp := markedMemoryLineageLastPresent_present (T := MarkedMemoryHistoryTracePopulation hZ history)
    (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history) (2*n+1) a
    ((markedMemoryLineagePresenceTimes_nonempty_iff _ _ _).mpr
      (markedMemoryHistoryTraceAddress_present hZ history a))
  exact ⟨markedMemoryLineagePresent_birthTime_le hp, markedMemoryLineageLastPresent_le _ _ _ _⟩

end
end ArtinMatthews
