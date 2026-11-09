module

public import ArtinMatthews.MarkedMemoryHistoryEdgeSlotOrigins
public import ArtinMatthews.MarkedMemoryHistoryEdgeDeaths


set_option backward.privateInPublic true
@[expose] public section

/-! Exact survival and fresh-birth existence after both actual slot
permutations. The source permutation relocates the singled-out last slot;
no old identity is identified with a numerically equal birth. -/
namespace ArtinMatthews
noncomputable section
variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
  (choice : MarkedMemoryEdgeChoice hZ s)

theorem markedMemoryEdgeSlotOrigin_old_range (old : MarkedMemoryPopulationIndex s) :
    Sum.inl old ∈ Set.range (markedMemoryEdgeSlotPopulationOrigin hZ s choice) ↔
      MarkedMemoryEdgeOldSurvives choice.2.1 ((markedMemorySlotPopulationEquiv choice.1 s).symm old) := by
  let e := markedMemorySlotPopulationEquiv choice.1 s
  let f := markedMemorySlotPopulationEquiv choice.2.2
    (markedRawEdgeTargetState hZ (markedRawSlotEquiv choice.1 s) choice.2.1)
  rw [← markedMemoryEdgeOrigin_old_range hZ (markedRawSlotEquiv choice.1 s) choice.2.1]
  constructor
  · rintro ⟨i,hi⟩
    refine ⟨f i,?_⟩
    have he := congrArg (Sum.map e.symm id) hi
    change Sum.map e.symm id (Sum.map e id
      (markedMemoryEdgePopulationOrigin hZ (markedRawSlotEquiv choice.1 s) choice.2.1 (f i))) =
      Sum.inl (e.symm old) at he
    generalize ho : markedMemoryEdgePopulationOrigin hZ (markedRawSlotEquiv choice.1 s) choice.2.1 (f i) = o at he ⊢
    cases o <;> simpa only [Sum.map_inl, Sum.map_inr, Equiv.symm_apply_apply, id_eq] using he
  · rintro ⟨i,hi⟩
    refine ⟨f.symm i,?_⟩
    change Sum.map e id
      (markedMemoryEdgePopulationOrigin hZ (markedRawSlotEquiv choice.1 s) choice.2.1
        (f (f.symm i))) = Sum.inl old
    simp only [Equiv.apply_symm_apply, hi, Sum.map_inl]
    exact congrArg Sum.inl (e.apply_symm_apply old)

theorem markedMemoryEdgeSlotOrigin_birth_range (birth : MarkedMemoryEdgeBirthIndex choice) :
    ∃! i, markedMemoryEdgeSlotPopulationOrigin hZ s choice i = Sum.inr birth := by
  obtain ⟨i,hi,_⟩ := markedMemoryEdgeOrigin_birth_range hZ (markedRawSlotEquiv choice.1 s) choice.2.1 birth
  let f := markedMemorySlotPopulationEquiv choice.2.2
    (markedRawEdgeTargetState hZ (markedRawSlotEquiv choice.1 s) choice.2.1)
  have hfi : markedMemoryEdgeSlotPopulationOrigin hZ s choice (f.symm i) = Sum.inr birth := by
    change Sum.map (markedMemorySlotPopulationEquiv choice.1 s) id
      (markedMemoryEdgePopulationOrigin hZ (markedRawSlotEquiv choice.1 s) choice.2.1
        (f (f.symm i))) = Sum.inr birth
    simp only [Equiv.apply_symm_apply, hi, Sum.map_inr, id_eq]
  exact ⟨f.symm i,hfi,fun k hk => (markedMemoryEdgeSlotPopulationOrigin hZ s choice).injective (hk.trans hfi.symm)⟩

end
end ArtinMatthews
