module

public import ArtinMatthews.MarkedMemoryHistoryGhostOrigins
public import ArtinMatthews.MarkedMemoryPopulationTransport
public import ArtinMatthews.MarkedMemoryQueueOrder


set_option backward.privateInPublic true
@[expose] public section

/-! Literal identity lists through a ghost and through state transport.
The survivor enumeration and birth enumeration retain their exact order. -/
namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {M B : ℕ} {Z : Finset (ℤ × ℤ)} {A : Type*}

theorem markedMemoryGhostOrigin_label_list
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P M B Z)
    (c : MarkedMemoryGhostChoice hZ s) (old : MarkedMemoryPopulationIndex s → A)
    (born : MarkedMemoryGhostBirthIndex c → A) (j : J) :
    List.ofFn (fun k => Sum.elim old born
      (markedMemoryGhostPopulationOrigin hZ s c (Sum.inr ⟨j,k⟩))) =
      List.ofFn (fun k => old (Sum.inr ⟨j,
        (markedRawGhostSurvivors s.2.2 c.deletion j).orderEmbOfFin rfl k⟩)) ++
      List.ofFn (fun k : Fin (c.sizes.1 j : ℕ) => born ⟨j,k⟩) := by
  rw [← List.ofFn_fin_append]
  congr 1
  funext k
  obtain ⟨x,rfl⟩ := finSumFinEquiv.surjective k
  cases x with
  | inl k =>
    simp only [finSumFinEquiv_apply_left, Fin.append, Fin.addCases_left]
    have he : Fin.castAdd (c.sizes.1 j : ℕ) k =
        (markedMemoryGhostOrigin s.2.2 c.deletion c.sizes j).symm
          (Sum.inl ((markedRawGhostSurvivors s.2.2 c.deletion j).orderIsoOfFin rfl k)) := by
      change Fin.castAdd _ k = Fin.castAdd _
        (((markedRawGhostSurvivors s.2.2 c.deletion j).orderIsoOfFin rfl).symm
          ((markedRawGhostSurvivors s.2.2 c.deletion j).orderIsoOfFin rfl k))
      rw [OrderIso.symm_apply_apply]
    rw [he,markedMemoryGhostPopulationOrigin_old]
    rfl
  | inr k =>
    simp only [finSumFinEquiv_apply_right, Fin.append, Fin.addCases_right]
    change Sum.elim old born (markedMemoryGhostPopulationOrigin hZ s c
      (Sum.inr ⟨j,(markedMemoryGhostOrigin s.2.2 c.deletion c.sizes j).symm (Sum.inr k)⟩)) = _
    rw [markedMemoryGhostPopulationOrigin_birth]
    rfl

theorem markedMemoryPopulationStateCast_pending_list
    {s t : MarkedRawState P M B Z} (h : s = t)
    (label : MarkedMemoryPopulationIndex t → A) (j : J) :
    List.ofFn (fun k => label (markedMemoryPopulationStateCast h (Sum.inr ⟨j,k⟩))) =
      List.ofFn (fun k => label (Sum.inr ⟨j,k⟩)) := by
  cases h
  rfl

end
end ArtinMatthews
