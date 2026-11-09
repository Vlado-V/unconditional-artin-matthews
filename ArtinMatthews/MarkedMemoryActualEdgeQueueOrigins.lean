module

public import ArtinMatthews.MarkedMemoryActualEdgeOrigins
public import ArtinMatthews.MarkedMemoryGhostOriginLists
public import ArtinMatthews.MarkedMemoryHistoryEdgeSlotDeaths


set_option backward.privateInPublic true
@[expose] public section

/-! Actual pending identities on both sides of an edge. Promotion and
store decisions are recovered from indexed origins and lifespan endpoints,
without identifying equal numeric prime values. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
  (history : MarkedMemoryChronologicalHistory hZ n s) (v : Fin n)

local notation "edge" => markedMemoryHistoryVertexEdge hZ history v
local notation "source" => markedMemoryGhostChoiceTarget hZ
  (markedMemoryHistoryVertexState hZ history v.castSucc) (markedMemoryHistoryVertexGhost hZ history v.castSucc)
local notation "target" => markedMemoryEdgeChoiceTarget hZ source edge
local notation "time" => 2*v.val+1

def markedMemoryActualEdgeSourcePendingIds (j : J) (k : Fin (source.2.2.1.1 j : ℕ)) :
    MarkedMemoryActualFiber hZ history j :=
  markedMemoryActualPendingIds hZ history time j
    (Fin.cast (congrArg (fun r : MarkedRawState P (pads+1) B Z => (r.2.2.1.1 j : ℕ))
      (markedMemoryHistoryEdgeSource_trace hZ history v).symm) k)

def markedMemoryActualEdgeTargetPendingIds (j : J) (k : Fin (target.2.2.1.1 j : ℕ)) :
    MarkedMemoryActualFiber hZ history j :=
  markedMemoryActualPendingIds hZ history (time+1) j
    (Fin.cast (congrArg (fun r : MarkedRawState P (pads+1) B Z => (r.2.2.1.1 j : ℕ))
      (markedMemoryActualEdgeTarget_trace hZ history v).symm) k)

theorem markedMemoryActualEdgeSourcePendingIds_val (j : J) (k : Fin (source.2.2.1.1 j : ℕ)) :
    (markedMemoryActualEdgeSourcePendingIds hZ history v j k).1 =
      markedMemoryActualEdgeSourceOrigin hZ history v (Sum.inr ⟨j,k⟩) := by
  unfold markedMemoryActualEdgeSourceOrigin
  change _ = markedMemoryActualOrigin hZ history time
    (markedMemoryPopulationStateCast (markedMemoryHistoryEdgeSource_trace hZ history v).symm (Sum.inr ⟨j,k⟩))
  rw [markedMemoryPopulationStateCast_pending]
  rfl

theorem markedMemoryActualEdgeTargetPendingIds_val (j : J) (k : Fin (target.2.2.1.1 j : ℕ)) :
    (markedMemoryActualEdgeTargetPendingIds hZ history v j k).1 =
      markedMemoryActualEdgeTargetOrigin hZ history v (Sum.inr ⟨j,k⟩) := by
  unfold markedMemoryActualEdgeTargetOrigin
  change _ = markedMemoryActualOrigin hZ history (time+1)
    (markedMemoryPopulationStateCast (markedMemoryActualEdgeTarget_trace hZ history v).symm (Sum.inr ⟨j,k⟩))
  rw [markedMemoryPopulationStateCast_pending]
  rfl

theorem markedMemoryActualEdgeSourcePendingIds_list (j : J) :
    List.ofFn (markedMemoryActualEdgeSourcePendingIds hZ history v j) =
      markedMemoryActualPendingQueue hZ history time j := by
  apply (List.map_injective_iff (f := Subtype.val)).mpr Subtype.val_injective
  simp only [List.map_ofFn, markedMemoryActualPendingQueue, Function.comp_def]
  simp_rw [markedMemoryActualEdgeSourcePendingIds_val]
  exact markedMemoryPopulationStateCast_pending_list
    (markedMemoryHistoryEdgeSource_trace hZ history v).symm
    (markedMemoryActualOrigin hZ history time) j

theorem markedMemoryActualEdgeTargetPendingIds_list (j : J) :
    List.ofFn (markedMemoryActualEdgeTargetPendingIds hZ history v j) =
      markedMemoryActualPendingQueue hZ history (time+1) j := by
  apply (List.map_injective_iff (f := Subtype.val)).mpr Subtype.val_injective
  simp only [List.map_ofFn, markedMemoryActualPendingQueue, Function.comp_def]
  simp_rw [markedMemoryActualEdgeTargetPendingIds_val]
  exact markedMemoryPopulationStateCast_pending_list
    (markedMemoryActualEdgeTarget_trace hZ history v).symm
    (markedMemoryActualOrigin hZ history (time+1)) j

theorem markedMemoryActualEdgeSourceOrigin_birthTime_le (old : MarkedMemoryPopulationIndex source) :
    markedMemoryLineageBirthTime (markedMemoryActualEdgeSourceOrigin hZ history v old) ≤ time := by
  exact markedMemoryLineageOrigin_birthTime_le
    (T := MarkedMemoryHistoryTracePopulation hZ history) (Birth := MarkedMemoryHistoryTraceBirth hZ history)
    (markedMemoryHistoryTraceStep hZ history) time
    (markedMemoryPopulationStateCast (markedMemoryHistoryEdgeSource_trace hZ history v).symm old)

theorem markedMemoryActualEdgeLabel_injective :
    Function.Injective (Sum.elim (markedMemoryActualEdgeSourceOrigin hZ history v)
      (markedMemoryActualEdgeBirthOrigin hZ history v)) := by
  intro a b h
  cases a with
  | inl olda =>
    cases b with
    | inl oldb =>
      exact congrArg Sum.inl ((markedMemoryActualEdgeSourceOrigin hZ history v).injective h)
    | inr born =>
      have hb := markedMemoryActualEdgeSourceOrigin_birthTime_le hZ history v olda
      change markedMemoryActualEdgeSourceOrigin hZ history v olda =
        markedMemoryActualEdgeBirthOrigin hZ history v born at h
      rw [h] at hb
      change time+1 ≤ time at hb
      omega
  | inr born =>
    cases b with
    | inl old =>
      have hb := markedMemoryActualEdgeSourceOrigin_birthTime_le hZ history v old
      change markedMemoryActualEdgeBirthOrigin hZ history v born =
        markedMemoryActualEdgeSourceOrigin hZ history v old at h
      rw [← h] at hb
      change time+1 ≤ time at hb
      omega
    | inr born' =>
      change (Sum.inr ⟨time,cast (markedMemoryHistoryVertexEdge_birthType hZ history v).symm born⟩ :
        MarkedMemoryHistoryTraceAddress hZ history) =
        Sum.inr ⟨time,cast (markedMemoryHistoryVertexEdge_birthType hZ history v).symm born'⟩ at h
      have hc := eq_of_heq (Sigma.mk.inj (Sum.inr.inj h)).2
      exact congrArg Sum.inr ((Equiv.cast (markedMemoryHistoryVertexEdge_birthType hZ history v).symm).injective hc)

theorem markedMemoryActualEdge_promote_iff (j : J) (k : Fin (source.2.2.1.1 j : ℕ)) :
    edge.2.1.promotions j = some k ↔
      markedMemoryActualEdgeSourcePendingIds hZ history v j k = markedMemoryActualIncoming hZ history v j := by
  have hi : (markedMemoryActualIncoming hZ history v j).1 =
      markedMemoryActualEdgeTargetOrigin hZ history v (Sum.inl ⟨j,(edge.2.2 j).symm (Fin.last pads)⟩) :=
    (markedMemoryActualEdgeTargetOrigin_active hZ history v j _).symm
  constructor
  · intro hk
    apply Subtype.ext
    rw [markedMemoryActualEdgeSourcePendingIds_val, hi]
    have he := markedMemoryActualEdgeOrigin hZ history v (Sum.inl ⟨j,(edge.2.2 j).symm (Fin.last pads)⟩)
    rw [markedMemoryEdgeSlotOrigin_last_some hZ source edge j k hk] at he
    exact he
  · intro heq
    have he := markedMemoryActualEdgeOrigin hZ history v (Sum.inl ⟨j,(edge.2.2 j).symm (Fin.last pads)⟩)
    have hv := congrArg Subtype.val heq
    rw [markedMemoryActualEdgeSourcePendingIds_val, hi] at hv
    have horigin : markedMemoryEdgeSlotPopulationOrigin hZ source edge
        (Sum.inl ⟨j,(edge.2.2 j).symm (Fin.last pads)⟩) = Sum.inl (Sum.inr ⟨j,k⟩) := by
      apply markedMemoryActualEdgeLabel_injective hZ history v
      exact he.trans hv.symm
    by_cases hn : edge.2.1.promotions j = none
    · rw [markedMemoryEdgeSlotOrigin_fresh hZ source edge ⟨j,hn⟩] at horigin
      cases horigin
    · obtain ⟨l,hl⟩ := Option.ne_none_iff_exists'.mp hn
      rw [markedMemoryEdgeSlotOrigin_last_some hZ source edge j l hl] at horigin
      have hlk : l = k := eq_of_heq (Sigma.mk.inj (Sum.inr.inj (Sum.inl.inj horigin))).2
      exact hl.trans (congrArg some hlk)

theorem markedMemoryActualEdge_old_survives_iff_last (old : MarkedMemoryPopulationIndex source) :
    Sum.inl old ∈ Set.range (markedMemoryEdgeSlotPopulationOrigin hZ source edge) ↔
      time < markedMemoryHistoryLifespanLast hZ history (markedMemoryActualEdgeSourceOrigin hZ history v old) := by
  constructor
  · rintro ⟨next, hn⟩
    have he := markedMemoryActualEdgeOrigin hZ history v next
    rw [hn] at he
    have hp : MarkedMemoryLineagePresent (markedMemoryHistoryTraceStep hZ history) (time+1)
        (markedMemoryActualEdgeSourceOrigin hZ history v old) :=
      ⟨markedMemoryPopulationStateCast (markedMemoryActualEdgeTarget_trace hZ history v).symm next, he.symm⟩
    have hl := ((markedMemoryHistory_lifespan_exact hZ history
      (markedMemoryActualEdgeSourceOrigin hZ history v old) (time+1)).mp ⟨by omega,hp⟩).2
    omega
  · intro hl
    have hb := markedMemoryActualEdgeSourceOrigin_birthTime_le hZ history v old
    obtain ⟨next, hn⟩ := ((markedMemoryHistory_lifespan_exact hZ history
      (markedMemoryActualEdgeSourceOrigin hZ history v old) (time+1)).mpr ⟨by omega,by omega⟩).2
    let next' := (markedMemoryPopulationStateCast (markedMemoryActualEdgeTarget_trace hZ history v).symm).symm next
    have he : markedMemoryActualEdgeTargetOrigin hZ history v next' =
        markedMemoryActualEdgeSourceOrigin hZ history v old := by
      change markedMemoryActualOrigin hZ history (time+1) next =
        markedMemoryActualEdgeSourceOrigin hZ history v old at hn
      change markedMemoryActualOrigin hZ history (time+1)
        ((markedMemoryPopulationStateCast (markedMemoryActualEdgeTarget_trace hZ history v).symm)
          ((markedMemoryPopulationStateCast (markedMemoryActualEdgeTarget_trace hZ history v).symm).symm next)) = _
      simpa only [Equiv.apply_symm_apply] using hn
    exact ⟨next',markedMemoryActualEdgeLabel_injective hZ history v
      ((markedMemoryActualEdgeOrigin hZ history v next').trans he)⟩

theorem markedMemoryActualEdge_store_iff_last (j : J) :
    edge.2.1.store j = true ↔
      time < markedMemoryActualLast hZ history j (markedMemoryActualOutgoing hZ history v j) := by
  have he := markedMemoryActualEdge_old_survives_iff_last hZ history v
    (Sum.inl ⟨j,edge.1 j (Fin.last pads)⟩)
  rw [markedMemoryEdgeSlotOrigin_old_range] at he
  change (((edge.1 j).symm (edge.1 j (Fin.last pads))) ≠ Fin.last pads ∨ edge.2.1.store j = true) ↔ _ at he
  rw [Equiv.symm_apply_apply] at he
  change edge.2.1.store j = true ↔ time < markedMemoryHistoryLifespanLast hZ history
    (markedMemoryActualOrigin hZ history time (Sum.inl ⟨j,edge.1 j (Fin.last pads)⟩))
  simpa only [ne_eq, not_true_eq_false, false_or, markedMemoryActualEdgeSourceOrigin_active] using he

theorem markedMemoryActualEdge_store_eq_decide_last (j : J) :
    edge.2.1.store j =
      decide (time < markedMemoryActualLast hZ history j (markedMemoryActualOutgoing hZ history v j)) := by
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using markedMemoryActualEdge_store_iff_last hZ history v j

end
end ArtinMatthews
