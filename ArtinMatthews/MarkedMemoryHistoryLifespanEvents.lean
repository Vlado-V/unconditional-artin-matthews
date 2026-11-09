module

public import ArtinMatthews.MarkedMemoryHistoryEventKinds


set_option backward.privateInPublic true
@[expose] public section

/-! The endpoints of computed actual lifespans are genuine local events.
A nonterminal final occurrence disappears on the next transition, whose
parity determines whether it is a pending ghost death or active edge death. -/
namespace ArtinMatthews
noncomputable section
variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
  (history : MarkedMemoryChronologicalHistory hZ n s)

theorem markedMemoryHistory_lifespan_death
    (a : MarkedMemoryHistoryTraceAddress hZ history)
    (ha : markedMemoryHistoryLifespanLast hZ history a < 2*n+1) :
    ∃ i : MarkedMemoryHistoryTracePopulation hZ history (markedMemoryHistoryLifespanLast hZ history a),
      markedMemoryLineageOrigin (T := MarkedMemoryHistoryTracePopulation hZ history)
          (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history)
          (markedMemoryHistoryLifespanLast hZ history a) i = a ∧
        Sum.inl i ∉ Set.range (markedMemoryHistoryTraceStep hZ history (markedMemoryHistoryLifespanLast hZ history a)) := by
  let hn := (markedMemoryLineagePresenceTimes_nonempty_iff
    (T := MarkedMemoryHistoryTracePopulation hZ history) (Birth := MarkedMemoryHistoryTraceBirth hZ history)
    (markedMemoryHistoryTraceStep hZ history) (2*n+1) a).mpr (markedMemoryHistoryTraceAddress_present hZ history a)
  have hp := markedMemoryLineageLastPresent_present (markedMemoryHistoryTraceStep hZ history) (2*n+1) a hn
  obtain ⟨i,hi⟩ := hp
  refine ⟨i,hi,?_⟩
  rintro ⟨next,hnext⟩
  have hnot := markedMemoryLineage_not_present_after_last
    (T := MarkedMemoryHistoryTracePopulation hZ history) (Birth := MarkedMemoryHistoryTraceBirth hZ history)
    (markedMemoryHistoryTraceStep hZ history) (2*n+1) a hn ha (Nat.lt_succ_self _)
  apply hnot
  refine ⟨next,?_⟩
  change Sum.elim
    (markedMemoryLineageOrigin (T := MarkedMemoryHistoryTracePopulation hZ history)
      (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history)
      (markedMemoryHistoryLifespanLast hZ history a))
    (fun b => Sum.inr ⟨markedMemoryHistoryLifespanLast hZ history a,b⟩)
    (markedMemoryHistoryTraceStep hZ history (markedMemoryHistoryLifespanLast hZ history a) next) = a
  rw [hnext]
  exact hi

/-- A computed even-step death is an actual pending ghost death. -/
theorem markedMemoryHistory_lifespan_death_pending
    (a : MarkedMemoryHistoryTraceAddress hZ history)
    (ha : markedMemoryHistoryLifespanLast hZ history a < 2*n+1)
    (ht : markedMemoryHistoryLifespanLast hZ history a % 2 = 0) :
    ∃ j k, markedMemoryLineageOrigin (T := MarkedMemoryHistoryTracePopulation hZ history)
      (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history)
      (markedMemoryHistoryLifespanLast hZ history a) (Sum.inr ⟨j,k⟩) = a := by
  obtain ⟨i,hi,hd⟩ := markedMemoryHistory_lifespan_death hZ history a ha
  obtain ⟨j,k,rfl⟩ := markedMemoryHistoryTrace_death_even hZ history _ i hd ht
  exact ⟨j,k,hi⟩

/-- A computed odd-step death is an actual unstored active edge death. -/
theorem markedMemoryHistory_lifespan_death_active
    (a : MarkedMemoryHistoryTraceAddress hZ history)
    (ha : markedMemoryHistoryLifespanLast hZ history a < 2*n+1)
    (ht : markedMemoryHistoryLifespanLast hZ history a % 2 = 1) :
    ∃ j k, markedMemoryLineageOrigin (T := MarkedMemoryHistoryTracePopulation hZ history)
      (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history)
      (markedMemoryHistoryLifespanLast hZ history a) (Sum.inl ⟨j,k⟩) = a := by
  obtain ⟨i,hi,hd⟩ := markedMemoryHistory_lifespan_death hZ history a ha
  obtain ⟨j,k,rfl⟩ := markedMemoryHistoryTrace_death_odd hZ history _ i hd ht
  exact ⟨j,k,hi⟩

/-- A ghost-born lifespan begins with an actual pending slot. -/
theorem markedMemoryHistory_lifespan_birth_pending (t : ℕ)
    (birth : MarkedMemoryHistoryTraceBirth hZ history t) (ht : t % 2 = 0) :
    ∃ j k, markedMemoryLineageOrigin (T := MarkedMemoryHistoryTracePopulation hZ history)
      (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history)
      (t+1) (Sum.inr ⟨j,k⟩) = Sum.inr ⟨t,birth⟩ := by
  obtain ⟨j,k,hk⟩ := markedMemoryHistoryTrace_birth_even hZ history t birth ht
  exact ⟨j,k,by simp only [markedMemoryLineageOrigin, hk, Sum.elim_inr]⟩

/-- A fresh edge-born lifespan begins with an actual active slot. -/
theorem markedMemoryHistory_lifespan_birth_active (t : ℕ)
    (birth : MarkedMemoryHistoryTraceBirth hZ history t) (ht : t % 2 = 1) :
    ∃ j k, markedMemoryLineageOrigin (T := MarkedMemoryHistoryTracePopulation hZ history)
      (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history)
      (t+1) (Sum.inl ⟨j,k⟩) = Sum.inr ⟨t,birth⟩ := by
  obtain ⟨j,k,hk⟩ := markedMemoryHistoryTrace_birth_odd hZ history t birth ht
  exact ⟨j,k,by simp only [markedMemoryLineageOrigin, hk, Sum.elim_inr]⟩

end
end ArtinMatthews
