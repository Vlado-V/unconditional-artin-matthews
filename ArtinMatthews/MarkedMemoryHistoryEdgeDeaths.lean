module

public import ArtinMatthews.MarkedMemoryHistoryEdgeOriginsPrime


set_option backward.privateInPublic true
@[expose] public section

/-! Exact image and death set of a canonical edge. Indexed identities, rather than
numeric prime values, determine survival. All pending particles survive, either by
promotion or in memory; an old last active slot survives exactly when it is stored. -/
namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z : Finset (ℤ × ℤ)}

/-- Only the last active slot of an unstored group dies at an edge. -/
def MarkedMemoryEdgeOldSurvives
    {hZ : ∀ z ∈ Z, IsCoprime z.1 z.2} {s : MarkedRawState P (pads+1) B Z}
    (choice : MarkedRawEdgeChoice hZ s) : MarkedMemoryPopulationIndex s → Prop :=
  Sum.elim (fun i => i.2 ≠ Fin.last pads ∨ choice.store i.1 = true) (fun _ => True)

variable (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
  (choice : MarkedRawEdgeChoice hZ s)

@[simp] theorem markedMemoryEdgePopulationOrigin_copied (j : J) (i : Fin pads) :
    markedMemoryEdgePopulationOrigin hZ s choice (Sum.inl ⟨j, i.castSucc⟩) =
      Sum.inl (Sum.inl ⟨j, i.castSucc⟩) := by
  rw [markedMemoryEdgePopulationOrigin_active, markedMemoryEdgeGroupOrigin_copied]
  rfl

@[simp] theorem markedMemoryEdgePopulationOrigin_survivor (j : J)
    (i : ↥(markedRawGhostSurvivors s.2.2 (markedRawEdgePromotionDeletion choice.promotions) j)) :
    markedMemoryEdgePopulationOrigin hZ s choice
      (Sum.inr ⟨j, (markedMemoryGhostOrigin s.2.2
        (markedRawEdgePromotionDeletion choice.promotions)
        (markedRawEdgeStoreSizes hZ s choice) j).symm (Sum.inl i)⟩) =
      Sum.inl (Sum.inr ⟨j, i.1⟩) := by
  erw [markedMemoryEdgePopulationOrigin_pending, markedMemoryEdgeGroupOrigin_survivor]
  rfl

@[simp] theorem markedMemoryEdgePopulationOrigin_store (j : J)
    (i : Fin ((markedRawEdgeStoreSizes hZ s choice).1 j : ℕ)) :
    markedMemoryEdgePopulationOrigin hZ s choice
      (Sum.inr ⟨j, (markedMemoryGhostOrigin s.2.2
        (markedRawEdgePromotionDeletion choice.promotions)
        (markedRawEdgeStoreSizes hZ s choice) j).symm (Sum.inr i)⟩) =
      Sum.inl (Sum.inl ⟨j, Fin.last pads⟩) := by
  erw [markedMemoryEdgePopulationOrigin_pending, markedMemoryEdgeGroupOrigin_store]
  rfl

@[simp] theorem markedMemoryEdgePopulationOrigin_last_none (j : J)
    (hn : choice.promotions j = none) :
    markedMemoryEdgePopulationOrigin hZ s choice (Sum.inl ⟨j, Fin.last pads⟩) =
      Sum.inr ⟨j, hn⟩ := by
  rw [markedMemoryEdgePopulationOrigin_active, markedMemoryEdgeGroupOrigin_last_none hZ s choice j hn]
  rfl

@[simp] theorem markedMemoryEdgePopulationOrigin_last_some (j : J)
    (k : Fin (s.2.2.1.1 j : ℕ)) (hk : choice.promotions j = some k) :
    markedMemoryEdgePopulationOrigin hZ s choice (Sum.inl ⟨j, Fin.last pads⟩) =
      Sum.inl (Sum.inr ⟨j, k⟩) := by
  rw [markedMemoryEdgePopulationOrigin_active,
    markedMemoryEdgeGroupOrigin_last_some hZ s choice j k hk]
  rfl

/-- The image of the genuine edge injection contains exactly the surviving old indices. -/
theorem markedMemoryEdgeOrigin_old_range (old : MarkedMemoryPopulationIndex s) :
    Sum.inl old ∈ Set.range (markedMemoryEdgePopulationOrigin hZ s choice) ↔
      MarkedMemoryEdgeOldSurvives choice old := by
  constructor
  · rintro ⟨i, hi⟩
    rcases i with ⟨j, k⟩ | ⟨j, k⟩
    · revert hi
      refine Fin.lastCases ?_ (fun k => ?_) k
      · intro hi
        by_cases hn : choice.promotions j = none
        · rw [markedMemoryEdgePopulationOrigin_last_none hZ s choice j hn] at hi
          cases hi
        · obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp hn
          rw [markedMemoryEdgePopulationOrigin_last_some hZ s choice j k hk] at hi
          cases Sum.inl.inj hi
          trivial
      · intro hi
        rw [markedMemoryEdgePopulationOrigin_copied] at hi
        cases Sum.inl.inj hi
        exact Or.inl k.castSucc_ne_last
    · obtain ⟨o, rfl⟩ := (markedMemoryGhostOrigin s.2.2
        (markedRawEdgePromotionDeletion choice.promotions)
        (markedRawEdgeStoreSizes hZ s choice) j).symm.surjective k
      cases o with
      | inl survivor =>
        rw [markedMemoryEdgePopulationOrigin_survivor] at hi
        cases Sum.inl.inj hi
        trivial
      | inr stored =>
        rw [markedMemoryEdgePopulationOrigin_store] at hi
        cases Sum.inl.inj hi
        right
        have hk := stored.isLt
        change (stored : ℕ) < (if choice.store j then 1 else 0) at hk
        cases hs : choice.store j <;> simp_all
  · intro h
    rcases old with ⟨j, k⟩ | ⟨j, k⟩
    · revert h
      refine Fin.lastCases ?_ (fun k => ?_) k
      · intro h
        have hs : choice.store j = true := by simpa [MarkedMemoryEdgeOldSurvives] using h
        let stored : Fin ((markedRawEdgeStoreSizes hZ s choice).1 j : ℕ) :=
          ⟨0, by change 0 < (if choice.store j then 1 else 0); simp [hs]⟩
        exact ⟨Sum.inr ⟨j, (markedMemoryGhostOrigin s.2.2
          (markedRawEdgePromotionDeletion choice.promotions)
          (markedRawEdgeStoreSizes hZ s choice) j).symm (Sum.inr stored)⟩,
          markedMemoryEdgePopulationOrigin_store hZ s choice j stored⟩
      · intro _
        exact ⟨Sum.inl ⟨j, k.castSucc⟩,
          markedMemoryEdgePopulationOrigin_copied hZ s choice j k⟩
    · by_cases hk : choice.promotions j = some k
      · exact ⟨Sum.inl ⟨j, Fin.last pads⟩,
          markedMemoryEdgePopulationOrigin_last_some hZ s choice j k hk⟩
      · have hsurv : k ∈ markedRawGhostSurvivors s.2.2
            (markedRawEdgePromotionDeletion choice.promotions) j := by
          simpa [markedRawGhostSurvivors, markedRawEdgePromotionDeletion] using hk
        exact ⟨Sum.inr ⟨j, (markedMemoryGhostOrigin s.2.2
          (markedRawEdgePromotionDeletion choice.promotions)
          (markedRawEdgeStoreSizes hZ s choice) j).symm (Sum.inl ⟨k, hsurv⟩)⟩,
          markedMemoryEdgePopulationOrigin_survivor hZ s choice j ⟨k, hsurv⟩⟩

/-- Every performed fresh birth has exactly one target slot. -/
theorem markedMemoryEdgeOrigin_birth_range (birth : {j : J // choice.promotions j = none}) :
    ∃! i, markedMemoryEdgePopulationOrigin hZ s choice i = Sum.inr birth := by
  refine ⟨Sum.inl ⟨birth.1, Fin.last pads⟩,
    markedMemoryEdgePopulationOrigin_last_none hZ s choice birth.1 birth.2, ?_⟩
  intro i hi
  exact (markedMemoryEdgePopulationOrigin hZ s choice).injective
    (hi.trans (markedMemoryEdgePopulationOrigin_last_none hZ s choice birth.1 birth.2).symm)

/-- The complement among old active identities consists exactly of unstored last slots. -/
theorem markedMemoryEdgeOrigin_active_death (j : J) (k : Fin (pads+1)) :
    Sum.inl (Sum.inl ⟨j, k⟩) ∉ Set.range (markedMemoryEdgePopulationOrigin hZ s choice) ↔
      k = Fin.last pads ∧ choice.store j = false := by
  rw [markedMemoryEdgeOrigin_old_range]
  simp [MarkedMemoryEdgeOldSurvives]

/-- Promotion changes a pending identity's location, never its existence. -/
theorem markedMemoryEdgeOrigin_pending_survives (j : J) (k : Fin (s.2.2.1.1 j : ℕ)) :
    Sum.inl (Sum.inr ⟨j, k⟩) ∈ Set.range (markedMemoryEdgePopulationOrigin hZ s choice) := by
  rw [markedMemoryEdgeOrigin_old_range]
  trivial

/-- Surviving old identities have a unique target location, even when their prime values repeat. -/
theorem markedMemoryEdgeOrigin_old_unique (old : MarkedMemoryPopulationIndex s)
    (h : MarkedMemoryEdgeOldSurvives choice old) :
    ∃! i, markedMemoryEdgePopulationOrigin hZ s choice i = Sum.inl old := by
  obtain ⟨i, hi⟩ := (markedMemoryEdgeOrigin_old_range hZ s choice old).mpr h
  exact ⟨i, hi, fun j hj => (markedMemoryEdgePopulationOrigin hZ s choice).injective
    (hj.trans hi.symm)⟩

/-- The entire actual image is the disjoint old-survivor/fresh-birth partition. -/
theorem markedMemoryEdgeOrigin_range :
    Set.range (markedMemoryEdgePopulationOrigin hZ s choice) =
      {o | Sum.elim (MarkedMemoryEdgeOldSurvives choice) (fun _ => True) o} := by
  ext o
  rcases o with old | birth
  · exact markedMemoryEdgeOrigin_old_range hZ s choice old
  · change (Sum.inr birth ∈ Set.range (markedMemoryEdgePopulationOrigin hZ s choice)) ↔ True
    constructor
    · intro _; trivial
    · intro _
      exact (markedMemoryEdgeOrigin_birth_range hZ s choice birth).exists

end
end ArtinMatthews
