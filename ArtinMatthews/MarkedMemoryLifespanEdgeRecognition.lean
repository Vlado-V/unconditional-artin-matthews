module

public import ArtinMatthews.MarkedMemoryLifespanEdgeReconstruction
public import ArtinMatthews.MarkedMemoryLifespanSurvival
public import ArtinMatthews.MarkedMemoryHistoryPromotionTrace


set_option backward.privateInPublic true
@[expose] public section

/-! Recover the first edge's store and promotion decisions from computed
lifespan endpoints and indexed source/target identity matching. No numeric
prime distinctness is needed to recognize an old promotion. -/
namespace ArtinMatthews
noncomputable section

universe u v

theorem markedMemoryLineage_next_origin_eq_old_iff {T : ℕ → Type u} {Birth : ℕ → Type v}
    (step : ∀ t, T (t+1) ↪ T t ⊕ Birth t) (t : ℕ) (next : T (t+1)) (old : T t) :
    markedMemoryLineageOrigin step (t+1) next = markedMemoryLineageOrigin step t old ↔
      step t next = Sum.inl old := by
  constructor
  · intro hn
    cases hs : step t next with
    | inl previous =>
      have he : previous = old := by
        apply markedMemoryLineageOrigin_injective step t
        simpa only [markedMemoryLineageOrigin, hs, Sum.elim_inl] using hn
      exact congrArg Sum.inl he
    | inr born =>
      have hb := congrArg markedMemoryLineageBirthTime hn
      have hle := markedMemoryLineageOrigin_birthTime_le step t old
      simp only [markedMemoryLineageOrigin, hs, Sum.elim_inr] at hb
      change t+1 = markedMemoryLineageBirthTime (markedMemoryLineageOrigin step t old) at hb
      omega
  · intro hn
    simp only [markedMemoryLineageOrigin, hn, Sum.elim_inl]

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
  (history : MarkedMemoryChronologicalHistory hZ (n+1) s)

def markedMemoryHistoryFirstEdgeSourceLast (j : J) : MarkedMemoryHistoryTraceAddress hZ history :=
  markedMemoryLineageOrigin (T := MarkedMemoryHistoryTracePopulation hZ history)
    (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history) 1
    (Sum.inl ⟨j,history.2.1.1 j (Fin.last pads)⟩)

def markedMemoryHistoryFirstEdgeTargetLast (j : J) : MarkedMemoryHistoryTraceAddress hZ history :=
  markedMemoryLineageOrigin (T := MarkedMemoryHistoryTracePopulation hZ history)
    (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history) 2
    (Sum.inl ⟨j,(history.2.1.2.2 j).symm (Fin.last pads)⟩)

def markedMemoryHistoryFirstEdgePending (j : J) :
    Fin ((markedMemoryGhostChoiceTarget hZ s history.1).2.2.1.1 j : ℕ) ↪
      MarkedMemoryHistoryTraceAddress hZ history where
  toFun k := markedMemoryLineageOrigin (T := MarkedMemoryHistoryTracePopulation hZ history)
    (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history) 1
      (Sum.inr ⟨j,k⟩)
  inj' := by
    intro a b hab
    change markedMemoryLineageOrigin (T := MarkedMemoryHistoryTracePopulation hZ history)
      (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history) 1
      (Sum.inr ⟨j,a⟩) = markedMemoryLineageOrigin (T := MarkedMemoryHistoryTracePopulation hZ history)
      (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history) 1
      (Sum.inr ⟨j,b⟩) at hab
    have h := markedMemoryLineageOrigin_injective (T := MarkedMemoryHistoryTracePopulation hZ history)
      (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history) 1 hab
    exact eq_of_heq (Sigma.mk.inj (Sum.inr.inj h)).2

/-- The source-last lifespan continues exactly for a stored old active
identity, after accounting for the literal source-slot permutation. -/
theorem markedMemoryHistory_first_edge_store_iff (j : J) :
    history.2.1.2.1.store j = true ↔
      1 < markedMemoryHistoryLifespanLast hZ history (markedMemoryHistoryFirstEdgeSourceLast hZ history j) := by
  have h := markedMemoryHistory_source_survives_iff_last hZ history 1 (by omega)
    (Sum.inl ⟨j,history.2.1.1 j (Fin.last pads)⟩)
  change (Sum.inl (Sum.inl ⟨j,history.2.1.1 j (Fin.last pads)⟩) ∈
    Set.range (markedMemoryEdgeSlotPopulationOrigin hZ (markedMemoryGhostChoiceTarget hZ s history.1) history.2.1)) ↔ _ at h
  rw [markedMemoryEdgeSlotOrigin_old_range] at h
  change (((history.2.1.1 j).symm (history.2.1.1 j (Fin.last pads))) ≠ Fin.last pads ∨
    history.2.1.2.1.store j = true) ↔ _ at h
  rw [Equiv.symm_apply_apply] at h
  simpa only [ne_eq, not_true_eq_false, false_or, markedMemoryHistoryFirstEdgeSourceLast] using h

theorem markedMemoryEdgeSlotOrigin_last_some {s₁ : MarkedRawState P (pads+1) B Z}
    (edge : MarkedMemoryEdgeChoice hZ s₁) (j : J) (k : Fin (s₁.2.2.1.1 j : ℕ))
    (hk : edge.2.1.promotions j = some k) :
    markedMemoryEdgeSlotPopulationOrigin hZ s₁ edge
      (Sum.inl ⟨j,(edge.2.2 j).symm (Fin.last pads)⟩) = Sum.inl (Sum.inr ⟨j,k⟩) := by
  let r : MarkedMemoryEdgePromotionIndex hZ edge := ⟨j,by rw [hk]; exact Option.some_ne_none k⟩
  have hr : markedMemoryEdgePromotionSlot hZ edge r = k :=
    Option.some.inj ((markedMemoryEdgePromotionSlot_spec hZ edge r).symm.trans hk)
  have h := markedMemoryEdgeSlotOrigin_promoted hZ edge r
  rw [hr] at h
  exact h

/-- The old pending index is recovered by equality of actual lineage
identities, even when other particles have the same numeric prime. -/
theorem markedMemoryHistory_first_edge_promote_iff (j : J)
    (k : Fin ((markedMemoryGhostChoiceTarget hZ s history.1).2.2.1.1 j : ℕ)) :
    history.2.1.2.1.promotions j = some k ↔
      markedMemoryHistoryFirstEdgePending hZ history j k =
        markedMemoryHistoryFirstEdgeTargetLast hZ history j := by
  have hiff := markedMemoryLineage_next_origin_eq_old_iff
    (T := MarkedMemoryHistoryTracePopulation hZ history) (Birth := MarkedMemoryHistoryTraceBirth hZ history)
    (markedMemoryHistoryTraceStep hZ history) 1
    (Sum.inl ⟨j,(history.2.1.2.2 j).symm (Fin.last pads)⟩) (Sum.inr ⟨j,k⟩)
  constructor
  · intro hk
    symm
    apply hiff.mpr
    exact markedMemoryEdgeSlotOrigin_last_some hZ history.2.1 j k hk
  · intro he
    have hh := hiff.mp he.symm
    change markedMemoryEdgeSlotPopulationOrigin hZ (markedMemoryGhostChoiceTarget hZ s history.1) history.2.1
      (Sum.inl ⟨j,(history.2.1.2.2 j).symm (Fin.last pads)⟩) = Sum.inl (Sum.inr ⟨j,k⟩) at hh
    by_cases hn : history.2.1.2.1.promotions j = none
    · rw [markedMemoryEdgeSlotOrigin_fresh hZ _ history.2.1 ⟨j,hn⟩] at hh
      cases hh
    · obtain ⟨i,hi⟩ := Option.ne_none_iff_exists'.mp hn
      rw [markedMemoryEdgeSlotOrigin_last_some hZ history.2.1 j i hi] at hh
      have hik : i = k := eq_of_heq (Sigma.mk.inj (Sum.inr.inj (Sum.inl.inj hh))).2
      exact hi.trans (congrArg some hik)

/-- The endpoint/identity matching algorithm returns exactly the original
old-only promotion option. -/
theorem markedMemoryHistory_first_edge_oldIndex (j : J) :
    markedMemoryLifespanOldIndex (markedMemoryHistoryFirstEdgePending hZ history j)
      (markedMemoryHistoryFirstEdgeTargetLast hZ history j) = history.2.1.2.1.promotions j := by
  apply Option.ext
  intro k
  rw [markedMemoryLifespanOldIndex_eq_some]
  exact (markedMemoryHistory_first_edge_promote_iff hZ history j k).symm

end
end ArtinMatthews
