module

public import ArtinMatthews.MarkedMemoryLifespanSlotMatching


set_option backward.privateInPublic true
@[expose] public section

/-! The exact pair of source/target slot permutations for copied active
identities. Source permutation last selects the outgoing index; inverse
target permutation last selects the incoming index. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

def MarkedMemorySlotPairCompatible {A : Type*} {pads : ℕ}
    (src dst : Fin (pads+1) ↪ A) (out inc : Fin (pads+1))
    (pair : Equiv.Perm (Fin (pads+1)) × Equiv.Perm (Fin (pads+1))) : Prop :=
  pair.1 (Fin.last pads) = out ∧ pair.2 inc = Fin.last pads ∧
    ∀ k : Fin pads, src (pair.1 k.castSucc) = dst (pair.2.symm k.castSucc)

abbrev MarkedMemorySlotPairFiber {A : Type*} {pads : ℕ}
    (src dst : Fin (pads+1) ↪ A) (out inc : Fin (pads+1)) :=
  {pair : Equiv.Perm (Fin (pads+1)) × Equiv.Perm (Fin (pads+1)) //
    MarkedMemorySlotPairCompatible src dst out inc pair}

variable {A : Type*} [DecidableEq A] {pads : ℕ}
  (src dst : Fin (pads+1) ↪ A) (out inc : Fin (pads+1))
  (hremaining : (markedMemoryBirthBatch src).erase (src out) =
    (markedMemoryBirthBatch dst).erase (dst inc))

include hremaining

def markedMemorySlotPairOfOrder (π : Equiv.Perm (Fin pads)) :
    Equiv.Perm (Fin (pads+1)) × Equiv.Perm (Fin (pads+1)) :=
  (markedMemoryOutgoingSlotPermutation out π,
    (markedMemoryOutgoingSlotPermutation inc
      (π.trans (markedMemoryRemainingSlotMatching src dst out inc hremaining))).symm)

theorem markedMemorySlotPairOfOrder_compatible (π : Equiv.Perm (Fin pads)) :
    MarkedMemorySlotPairCompatible src dst out inc (markedMemorySlotPairOfOrder src dst out inc hremaining π) := by
  refine ⟨markedMemoryOutgoingSlotPermutation_last out π, ?_, ?_⟩
  · apply (markedMemoryOutgoingSlotPermutation inc
      (π.trans (markedMemoryRemainingSlotMatching src dst out inc hremaining))).injective
    simp only [markedMemorySlotPairOfOrder, Equiv.apply_symm_apply, markedMemoryOutgoingSlotPermutation_last]
  · intro k
    change src (markedMemoryOutgoingSlotPermutation out π k.castSucc) =
      dst (markedMemoryOutgoingSlotPermutation inc
        (π.trans (markedMemoryRemainingSlotMatching src dst out inc hremaining)) k.castSucc)
    rw [markedMemoryOutgoingSlotPermutation_castSucc, markedMemoryOutgoingSlotPermutation_castSucc]
    exact (markedMemoryRemainingSlotMatching_apply src dst out inc hremaining (π k)).symm

def markedMemorySlotFiberOfOrder (π : Equiv.Perm (Fin pads)) : MarkedMemorySlotPairFiber src dst out inc :=
  ⟨markedMemorySlotPairOfOrder src dst out inc hremaining π,
    markedMemorySlotPairOfOrder_compatible src dst out inc hremaining π⟩

theorem markedMemorySlotFiberOfOrder_injective :
    Function.Injective (markedMemorySlotFiberOfOrder src dst out inc hremaining) := by
  intro π ρ h
  have hs := congrArg (fun pair : MarkedMemorySlotPairFiber src dst out inc => pair.1.1) h
  apply Equiv.ext
  intro k
  have hk := congrArg (fun σ : Equiv.Perm (Fin (pads+1)) => σ k.castSucc) hs
  change markedMemoryOutgoingSlotPermutation out π k.castSucc =
    markedMemoryOutgoingSlotPermutation out ρ k.castSucc at hk
  rw [markedMemoryOutgoingSlotPermutation_castSucc, markedMemoryOutgoingSlotPermutation_castSucc] at hk
  exact Fin.castSucc_inj.mp ((Equiv.swap (Fin.last pads) out).injective hk)

theorem markedMemorySlotFiberOfOrder_surjective :
    Function.Surjective (markedMemorySlotFiberOfOrder src dst out inc hremaining) := by
  intro pair
  have hb : markedMemoryBirthBatch (markedMemoryRemainingSlotEmbedding src out) =
      markedMemoryBirthBatch (markedMemoryCopiedSlotEmbedding src pair.1.1) := by
    rw [markedMemoryRemainingSlotEmbedding_batch,
      markedMemoryCopiedSlotEmbedding_batch src pair.1.1 out pair.2.1]
  obtain ⟨π,hπ,_⟩ := (markedMemoryBirth_eq_iff_reindex _ _).mp hb
  have hσ : markedMemoryOutgoingSlotPermutation out π = pair.1.1 := by
    apply Equiv.ext
    intro i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · exact (markedMemoryOutgoingSlotPermutation_last out π).trans pair.2.1.symm
    · rw [markedMemoryOutgoingSlotPermutation_castSucc]
      apply src.injective
      exact congrArg (fun e : Fin pads ↪ A => e k) hπ
  have hτ : markedMemoryOutgoingSlotPermutation inc
      (π.trans (markedMemoryRemainingSlotMatching src dst out inc hremaining)) = pair.1.2.symm := by
    apply Equiv.ext
    intro i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · have hi : pair.1.2.symm (Fin.last pads) = inc := by
        apply pair.1.2.injective
        rw [Equiv.apply_symm_apply, pair.2.2.1]
      exact (markedMemoryOutgoingSlotPermutation_last inc _).trans hi.symm
    · apply dst.injective
      rw [markedMemoryOutgoingSlotPermutation_castSucc]
      have hc := pair.2.2.2 k
      rw [← hσ, markedMemoryOutgoingSlotPermutation_castSucc] at hc
      exact (markedMemoryRemainingSlotMatching_apply src dst out inc hremaining (π k)).trans hc
  refine ⟨π, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · exact hσ
  · change (markedMemoryOutgoingSlotPermutation inc
      (π.trans (markedMemoryRemainingSlotMatching src dst out inc hremaining))).symm = pair.1.2
    simpa only [Equiv.symm_symm] using congrArg Equiv.symm hτ

/-- Exactly one free copied-slot ordering remains after the outgoing and
incoming slots and all copied identities are fixed. -/
def markedMemorySlotPairFiberEquiv : MarkedMemorySlotPairFiber src dst out inc ≃ Equiv.Perm (Fin pads) :=
  (Equiv.ofBijective (markedMemorySlotFiberOfOrder src dst out inc hremaining)
    ⟨markedMemorySlotFiberOfOrder_injective src dst out inc hremaining,
      markedMemorySlotFiberOfOrder_surjective src dst out inc hremaining⟩).symm

theorem markedMemorySlotPair_exists :
    ∃ σ τ : Equiv.Perm (Fin (pads+1)), σ (Fin.last pads) = out ∧ τ inc = Fin.last pads ∧
      ∀ k : Fin pads, src (σ k.castSucc) = dst (τ.symm k.castSucc) := by
  let pair := markedMemorySlotFiberOfOrder src dst out inc hremaining (Equiv.refl _)
  exact ⟨pair.1.1, pair.1.2, pair.2⟩

theorem markedMemorySlotPairFiber_card :
    Fintype.card (MarkedMemorySlotPairFiber src dst out inc) = pads.factorial := by
  rw [Fintype.card_congr (markedMemorySlotPairFiberEquiv src dst out inc hremaining),
    Fintype.card_perm, Fintype.card_fin]

end
end ArtinMatthews
