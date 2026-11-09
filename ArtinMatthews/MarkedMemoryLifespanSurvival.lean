module

public import ArtinMatthews.MarkedMemoryHistoryLifespanEvents


set_option backward.privateInPublic true
@[expose] public section

/-! A source identity continues across a transition exactly when its
computed lifespan ends later. This recovers local death decisions from
actual endpoints, without numeric-prime distinctness. -/
namespace ArtinMatthews
noncomputable section

universe u v

theorem markedMemoryLineage_next_present_iff_range {T : ℕ → Type u} {Birth : ℕ → Type v}
    (step : ∀ t, T (t+1) ↪ T t ⊕ Birth t) (t : ℕ) (old : T t) :
    MarkedMemoryLineagePresent step (t+1) (markedMemoryLineageOrigin step t old) ↔
      Sum.inl old ∈ Set.range (step t) := by
  constructor
  · rintro ⟨next, hn⟩
    cases hs : step t next with
    | inl previous =>
      have he : previous = old := by
        apply markedMemoryLineageOrigin_injective step t
        simpa only [markedMemoryLineageOrigin, hs, Sum.elim_inl] using hn
      exact ⟨next,hs.trans (congrArg Sum.inl he)⟩
    | inr born =>
      have hb := congrArg markedMemoryLineageBirthTime hn
      have hle := markedMemoryLineageOrigin_birthTime_le step t old
      simp only [markedMemoryLineageOrigin, hs, Sum.elim_inr] at hb
      change t+1 = markedMemoryLineageBirthTime (markedMemoryLineageOrigin step t old) at hb
      omega
  · rintro ⟨next,hn⟩
    exact ⟨next,by simp only [markedMemoryLineageOrigin, hn, Sum.elim_inl]⟩

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
  (history : MarkedMemoryChronologicalHistory hZ n s)

theorem markedMemoryHistory_source_survives_iff_last (t : ℕ) (ht : t < 2*n+1)
    (old : MarkedMemoryHistoryTracePopulation hZ history t) :
    Sum.inl old ∈ Set.range (markedMemoryHistoryTraceStep hZ history t) ↔
      t < markedMemoryHistoryLifespanLast hZ history
        (markedMemoryLineageOrigin (T := MarkedMemoryHistoryTracePopulation hZ history)
          (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history) t old) := by
  let a := markedMemoryLineageOrigin (T := MarkedMemoryHistoryTracePopulation hZ history)
    (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history) t old
  have hb : markedMemoryLineageBirthTime a ≤ t :=
    markedMemoryLineageOrigin_birthTime_le (markedMemoryHistoryTraceStep hZ history) t old
  change _ ↔ t < markedMemoryHistoryLifespanLast hZ history a
  have hn := markedMemoryLineage_next_present_iff_range
    (T := MarkedMemoryHistoryTracePopulation hZ history) (Birth := MarkedMemoryHistoryTraceBirth hZ history)
    (markedMemoryHistoryTraceStep hZ history) t old
  constructor
  · intro hr
    have h := (markedMemoryHistory_lifespan_exact hZ history a (t+1)).mp ⟨by omega,hn.mpr hr⟩
    omega
  · intro hl
    exact hn.mp ((markedMemoryHistory_lifespan_exact hZ history a (t+1)).mpr ⟨by omega,by omega⟩).2

theorem markedMemoryHistory_source_dies_iff_last (t : ℕ) (ht : t < 2*n+1)
    (old : MarkedMemoryHistoryTracePopulation hZ history t) :
    Sum.inl old ∉ Set.range (markedMemoryHistoryTraceStep hZ history t) ↔
      markedMemoryHistoryLifespanLast hZ history
        (markedMemoryLineageOrigin (T := MarkedMemoryHistoryTracePopulation hZ history)
          (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history) t old) = t := by
  have hp := (markedMemoryHistory_lifespan_exact hZ history
    (markedMemoryLineageOrigin (T := MarkedMemoryHistoryTracePopulation hZ history)
      (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history) t old) t).mp
      ⟨Nat.le_of_lt ht,old,rfl⟩
  rw [markedMemoryHistory_source_survives_iff_last hZ history t ht]
  omega

/-- The first actual deletion mask is recoverable from computed lifespan
endpoints of the initial pending identities. -/
theorem markedMemoryHistory_head_ghost_deleted_iff_last (j : J) (k : Fin (s.2.2.1.1 j : ℕ)) :
    k ∈ (markedMemoryHistoryHeadGhost hZ history).deletion j ↔
      markedMemoryHistoryLifespanLast hZ history (Sum.inl (Sum.inr ⟨j,k⟩)) = 0 := by
  have h := markedMemoryHistory_source_dies_iff_last hZ history 0 (by omega) (Sum.inr ⟨j,k⟩)
  rw [← markedMemoryGhostOrigin_pending_death hZ s (markedMemoryHistoryHeadGhost hZ history) j k]
  cases n <;> exact h

theorem markedMemoryHistory_head_ghost_retained_iff_last (j : J) (k : Fin (s.2.2.1.1 j : ℕ)) :
    k ∈ markedRawGhostSurvivors s.2.2 (markedMemoryHistoryHeadGhost hZ history).deletion j ↔
      0 < markedMemoryHistoryLifespanLast hZ history (Sum.inl (Sum.inr ⟨j,k⟩)) := by
  simp only [markedRawGhostSurvivors, Finset.mem_sdiff, Finset.mem_univ, true_and,
    markedMemoryHistory_head_ghost_deleted_iff_last]
  omega

end
end ArtinMatthews
