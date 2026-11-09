module

public import ArtinMatthews.MarkedMemoryLifespanSlotMass
public import ArtinMatthews.MarkedMemoryHistoryEdgeDeaths
public import ArtinMatthews.MarkedMemoryHistoryEdgeSlotOrigins


set_option backward.privateInPublic true
@[expose] public section

/-! An actual copied-slot match gives the active-set exchange law.
The common survivor set is derived from the two genuine permutations. -/
namespace ArtinMatthews
noncomputable section

theorem markedMemoryCopiedActive_exchange {A : Type*} [DecidableEq A] {pads : ℕ}
    (src dst : Fin (pads+1) ↪ A) (σ τ : Equiv.Perm (Fin (pads+1)))
    (hc : ∀ k : Fin pads, src (σ k.castSucc) = dst (τ.symm k.castSucc)) (a : A) :
    (∃ i, dst i = a) ↔
      ((∃ i, src i = a) ∧ a ≠ src (σ (Fin.last pads))) ∨ a = dst (τ.symm (Fin.last pads)) := by
  have hpair : MarkedMemorySlotPairCompatible src dst (σ (Fin.last pads)) (τ.symm (Fin.last pads)) (σ,τ) :=
    ⟨rfl,τ.apply_symm_apply _,hc⟩
  have hr := markedMemorySlotPairCompatible_remaining src dst _ _ (σ,τ) hpair
  have hm : dst (τ.symm (Fin.last pads)) ∈ markedMemoryBirthBatch dst := by
    simp only [markedMemoryBirthBatch, Finset.mem_map, Finset.mem_univ, true_and]
    exact ⟨_,rfl⟩
  have hb : markedMemoryBirthBatch dst = insert (dst (τ.symm (Fin.last pads)))
      ((markedMemoryBirthBatch src).erase (src (σ (Fin.last pads)))) := by
    rw [hr]
    exact (Finset.insert_erase hm).symm
  have h := Finset.ext_iff.mp hb a
  simp only [markedMemoryBirthBatch, Finset.mem_map, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_erase] at h
  tauto

theorem markedMemoryEdgeSlotOrigin_copied_index {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (edge : MarkedMemoryEdgeChoice hZ s) (j : J) (k : Fin pads) :
    markedMemoryEdgeSlotPopulationOrigin hZ s edge (Sum.inl ⟨j,(edge.2.2 j).symm k.castSucc⟩) =
      Sum.inl (Sum.inl ⟨j,edge.1 j k.castSucc⟩) := by
  change Sum.map (markedMemorySlotPopulationEquiv edge.1 s) id
    (markedMemoryEdgePopulationOrigin hZ (markedRawSlotEquiv edge.1 s) edge.2.1
      (Sum.inl ⟨j,edge.2.2 j ((edge.2.2 j).symm k.castSucc)⟩)) = _
  rw [Equiv.apply_symm_apply, markedMemoryEdgePopulationOrigin_copied]
  rfl

theorem markedMemoryEdgeSlotOrigin_last_some {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (edge : MarkedMemoryEdgeChoice hZ s) (j : J) (k : Fin (s.2.2.1.1 j : ℕ))
    (hk : edge.2.1.promotions j = some k) :
    markedMemoryEdgeSlotPopulationOrigin hZ s edge (Sum.inl ⟨j,(edge.2.2 j).symm (Fin.last pads)⟩) =
      Sum.inl (Sum.inr ⟨j,k⟩) := by
  change Sum.map (markedMemorySlotPopulationEquiv edge.1 s) id
    (markedMemoryEdgePopulationOrigin hZ (markedRawSlotEquiv edge.1 s) edge.2.1
      (Sum.inl ⟨j,edge.2.2 j ((edge.2.2 j).symm (Fin.last pads))⟩)) = _
  rw [Equiv.apply_symm_apply, markedMemoryEdgePopulationOrigin_last_some hZ _ edge.2.1 j k hk]
  rfl

end
end ArtinMatthews
