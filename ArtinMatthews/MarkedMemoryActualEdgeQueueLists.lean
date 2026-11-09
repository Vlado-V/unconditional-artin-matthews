module

public import ArtinMatthews.MarkedMemoryActualEdgeQueueOrigins
public import ArtinMatthews.MarkedMemoryEdgeOriginLabels
public import ArtinMatthews.MarkedMemoryOfFnFilter


set_option backward.privateInPublic true
@[expose] public section

/-! Exact ordered pending-label lists through a raw edge and both slot
permutations. The list consists of increasing old survivor indices followed
by the actual optional stored source identity. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z : Finset (ℤ × ℤ)}

theorem markedMemoryRawEdgeOrigin_pending_list {A : Type*}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (c : MarkedRawEdgeChoice hZ s) (old : MarkedMemoryPopulationIndex s → A)
    (born : {j : J // c.promotions j = none} → A) (j : J) :
    List.ofFn (fun k => Sum.elim old born
      (markedMemoryEdgePopulationOrigin hZ s c (Sum.inr ⟨j,k⟩))) =
      List.ofFn (fun k => old (Sum.inr ⟨j,
        (markedRawGhostSurvivors s.2.2 (markedRawEdgePromotionDeletion c.promotions) j).orderEmbOfFin rfl k⟩)) ++
      List.ofFn (fun _ : Fin (if c.store j then 1 else 0) => old (Sum.inl ⟨j,Fin.last pads⟩)) := by
  let keep := markedRawGhostSurvivors s.2.2 (markedRawEdgePromotionDeletion c.promotions) j
  rw [← List.ofFn_fin_append]
  congr 1
  funext k
  obtain ⟨o,rfl⟩ := (finSumFinEquiv : Fin keep.card ⊕ Fin (if c.store j then 1 else 0) ≃ _).surjective k
  cases o with
  | inl i =>
    have hidx : (markedMemoryGhostOrigin s.2.2 (markedRawEdgePromotionDeletion c.promotions)
        (markedRawEdgeStoreSizes hZ s c) j).symm (Sum.inl (keep.orderIsoOfFin rfl i)) =
        finSumFinEquiv (Sum.inl i) := by
      change finSumFinEquiv (Sum.inl ((keep.orderIsoOfFin rfl).symm ((keep.orderIsoOfFin rfl) i))) =
        finSumFinEquiv (Sum.inl i)
      rw [OrderIso.symm_apply_apply]
    have h := markedMemoryEdgePopulationOrigin_survivor hZ s c j (keep.orderIsoOfFin rfl i)
    rw [hidx] at h
    simp only [Fin.append, finSumFinEquiv_apply_left, Fin.addCases_left]
    exact congrArg (Sum.elim old born) h
  | inr i =>
    have hidx : (markedMemoryGhostOrigin s.2.2 (markedRawEdgePromotionDeletion c.promotions)
        (markedRawEdgeStoreSizes hZ s c) j).symm (Sum.inr i) =
        finSumFinEquiv (Sum.inr i) := by
      rfl
    have h := markedMemoryEdgePopulationOrigin_store hZ s c j i
    rw [hidx] at h
    dsimp only [keep]
    simp only [Fin.append, finSumFinEquiv_apply_right, Fin.addCases_right]
    exact congrArg (Sum.elim old born) h

theorem markedMemorySlotEdgeOrigin_pending_list {A : Type*}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (c : MarkedMemoryEdgeChoice hZ s) (old : MarkedMemoryPopulationIndex s → A)
    (born : MarkedMemoryEdgeBirthIndex c → A) (j : J) :
    List.ofFn (fun k => Sum.elim old born
      (markedMemoryEdgeSlotPopulationOrigin hZ s c (Sum.inr ⟨j,k⟩))) =
      List.ofFn (fun k => old (Sum.inr ⟨j,
        (markedRawGhostSurvivors s.2.2 (markedRawEdgePromotionDeletion c.2.1.promotions) j).orderEmbOfFin rfl k⟩)) ++
      List.ofFn (fun _ : Fin (if c.2.1.store j then 1 else 0) =>
        old (Sum.inl ⟨j,c.1 j (Fin.last pads)⟩)) := by
  calc
    _ = List.ofFn (fun k => Sum.elim
        (fun i => old (markedMemorySlotPopulationEquiv c.1 s i)) born
        (markedMemoryEdgePopulationOrigin hZ (markedRawSlotEquiv c.1 s) c.2.1 (Sum.inr ⟨j,k⟩))) := by
      congr 1
      funext k
      change Sum.elim old born (Sum.map (markedMemorySlotPopulationEquiv c.1 s) id
        (markedMemoryEdgePopulationOrigin hZ (markedRawSlotEquiv c.1 s) c.2.1 (Sum.inr ⟨j,k⟩))) = _
      cases markedMemoryEdgePopulationOrigin hZ (markedRawSlotEquiv c.1 s) c.2.1 (Sum.inr ⟨j,k⟩) <;> rfl
    _ = _ := markedMemoryRawEdgeOrigin_pending_list hZ (markedRawSlotEquiv c.1 s) c.2.1
      (fun i => old (markedMemorySlotPopulationEquiv c.1 s i)) born j

variable {n : ℕ} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
  {s : MarkedRawState P (pads+1) B Z}
  (history : MarkedMemoryChronologicalHistory hZ n s) (v : Fin n)

local notation "edge" => markedMemoryHistoryVertexEdge hZ history v
local notation "source" => markedMemoryGhostChoiceTarget hZ
  (markedMemoryHistoryVertexState hZ history v.castSucc) (markedMemoryHistoryVertexGhost hZ history v.castSucc)

theorem markedMemoryActualEdge_pending_append (j : J) :
    List.ofFn (markedMemoryActualEdgeTargetPendingIds hZ history v j) =
      List.ofFn (fun k => markedMemoryActualEdgeSourcePendingIds hZ history v j
        ((markedRawGhostSurvivors source.2.2 (markedRawEdgePromotionDeletion edge.2.1.promotions) j).orderEmbOfFin rfl k)) ++
      List.ofFn (fun _ : Fin (if edge.2.1.store j then 1 else 0) =>
        markedMemoryActualOutgoing hZ history v j) := by
  apply (List.map_injective_iff (f := Subtype.val)).mpr Subtype.val_injective
  simp only [List.map_ofFn, List.map_append, Function.comp_def]
  simp_rw [markedMemoryActualEdgeTargetPendingIds_val, markedMemoryActualEdgeSourcePendingIds_val]
  have h := markedMemorySlotEdgeOrigin_pending_list hZ source edge
    (markedMemoryActualEdgeSourceOrigin hZ history v) (markedMemoryActualEdgeBirthOrigin hZ history v) j
  simp_rw [markedMemoryActualEdgeOrigin, markedMemoryActualEdgeSourceOrigin_active] at h
  exact h

end
end ArtinMatthews
