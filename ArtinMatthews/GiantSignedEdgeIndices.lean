module

public import ArtinMatthews.GiantSignedGhostRow
public import ArtinMatthews.GiantTwoSidedPatternCompletions
public import Mathlib.Data.Fintype.CardEmbedding


set_option backward.privateInPublic true
@[expose] public section

/-! The actual target slots inject into old memory indices. Their ordered
enumeration is an old-index subset together with its retrieval order. -/

namespace ArtinMatthews
open scoped BigOperators
noncomputable section

abbrev GiantSignedOrderedPromotion (k a : ℕ) :=
  Σ _ : MarkedRawDeletionBatch k a, Equiv.Perm (Fin a)

def giantSignedPromotionEmbedding {k a : ℕ} (c : GiantSignedOrderedPromotion k a) :
    Fin a ↪ Fin k :=
  c.2.toEmbedding.trans (c.1.1.orderEmbOfFin (markedRawDeletionBatch_deleted_card c.1)).toEmbedding

theorem giantSignedPromotionEmbedding_image {k a : ℕ} (c : GiantSignedOrderedPromotion k a) :
    Finset.univ.map (giantSignedPromotionEmbedding c) = c.1.1 := by
  unfold giantSignedPromotionEmbedding
  rw [← Finset.map_map, Finset.map_univ_equiv, Finset.map_orderEmbOfFin_univ]

theorem giantSignedPromotionEmbedding_injective (k a : ℕ) :
    Function.Injective (@giantSignedPromotionEmbedding k a) := by
  rintro ⟨S, σ⟩ ⟨T, τ⟩ h
  have hST : S = T := Subtype.ext (by
    rw [← giantSignedPromotionEmbedding_image ⟨S, σ⟩,
      ← giantSignedPromotionEmbedding_image ⟨T, τ⟩, h])
  subst T
  congr 1
  apply Equiv.ext
  intro i
  apply (S.1.orderEmbOfFin (markedRawDeletionBatch_deleted_card S)).injective
  exact DFunLike.congr_fun h i

theorem giantSignedPromotionEmbedding_surjective (k a : ℕ) :
    Function.Surjective (@giantSignedPromotionEmbedding k a) := by
  intro e
  let S : Finset (Fin k) := Finset.univ.map e
  have hS : S.card = a := by simp only [S, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  let batch : MarkedRawDeletionBatch k a :=
    ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hS⟩⟩
  let order : Fin a ≃ ↥S := (S.orderIsoOfFin hS).toEquiv
  let f : Fin a → Fin a := fun i => order.symm ⟨e i, Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  have hf : Function.Injective f := by
    intro i j h
    apply e.injective
    have he := congrArg (fun z : Fin a => (order z).val) h
    simpa only [f, Equiv.apply_symm_apply] using he
  let σ : Equiv.Perm (Fin a) := Equiv.ofBijective f ⟨hf, Finite.surjective_of_injective hf⟩
  refine ⟨⟨batch, σ⟩, ?_⟩
  apply Function.Embedding.ext
  intro i
  change (S.orderIsoOfFin hS (f i)).val = e i
  exact congrArg Subtype.val (order.apply_symm_apply _)

def giantSignedPromotionIndexEquiv (k a : ℕ) :
    GiantSignedOrderedPromotion k a ≃ (Fin a ↪ Fin k) :=
  Equiv.ofBijective giantSignedPromotionEmbedding
    ⟨giantSignedPromotionEmbedding_injective k a, giantSignedPromotionEmbedding_surjective k a⟩

theorem giantSignedPromotionIndexEquiv_apply {k a : ℕ} (c : GiantSignedOrderedPromotion k a) :
    giantSignedPromotionIndexEquiv k a c = giantSignedPromotionEmbedding c := rfl

theorem giantSignedPromotionIndex_count (n a : ℕ) :
    (Fintype.card (Fin a ↪ Fin (n + a))) * Nat.factorial n = Nat.factorial (n + a) := by
  rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]
  have h := Nat.factorial_mul_descFactorial (show a ≤ n + a by omega)
  simpa only [Nat.add_sub_cancel_right, Nat.mul_comm] using h

theorem giantSignedPatternFreeSlots_card {k : ℕ} (C : Finset (Fin k)) (ell : ℕ) :
    Fintype.card (GiantTwoSidedPatternFreeSlots C ell) = ell + C.card := by
  simp only [GiantTwoSidedPatternFreeSlots, Fintype.card_sum, Fintype.card_coe,
    Fintype.card_fin, Nat.add_comm]

def giantSignedPatternFreeSlotEquiv {k : ℕ} (C : Finset (Fin k)) (ell : ℕ) :
    Fin (ell + C.card) ≃ GiantTwoSidedPatternFreeSlots C ell :=
  (finCongr (Nat.add_comm ell C.card)).trans
    (finSumFinEquiv.symm.trans (Equiv.sumCongr (C.orderIsoOfFin rfl).toEquiv (Equiv.refl _)))

end
end ArtinMatthews
