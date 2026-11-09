module

public import ArtinMatthews.GiantSignedEdgeMemory


set_option backward.privateInPublic true
@[expose] public section

/-! Ordered promotions into an actual set of hit indices. The cardinality
counts indices, including distinct old indices with equal particle values. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def giantSignedEmbeddingIntoFinsetEquiv {n a : ℕ} (E : Finset (Fin n)) :
    {e : Fin a ↪ Fin n // ∀ i, e i ∈ E} ≃ (Fin a ↪ E) where
  toFun e := ⟨fun i => ⟨e.val i, e.property i⟩,
    fun _ _ h => e.val.injective (congrArg Subtype.val h)⟩
  invFun e := ⟨e.trans (Function.Embedding.subtype _), fun i => (e i).property⟩
  left_inv e := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro i
    rfl
  right_inv e := by
    apply Function.Embedding.ext
    intro i
    rfl

theorem giantSignedEmbeddingIntoFinset_card {n a : ℕ} (E : Finset (Fin n)) :
    Fintype.card {e : Fin a ↪ Fin n // ∀ i, e i ∈ E} = E.card.descFactorial a := by
  classical
  rw [Fintype.card_congr (giantSignedEmbeddingIntoFinsetEquiv E),
    Fintype.card_embedding_eq, Fintype.card_coe, Fintype.card_fin]

def giantSignedPromotionFamilyIntoFinsetsEquiv {J : Type*} {n a : J → ℕ}
    (E : (j : J) → Finset (Fin (n j))) :
    {e : (j : J) → Fin (a j) ↪ Fin (n j) // ∀ j i, e j i ∈ E j} ≃
      ((j : J) → {e : Fin (a j) ↪ Fin (n j) // ∀ i, e i ∈ E j}) where
  toFun e j := ⟨e.val j, e.property j⟩
  invFun e := ⟨fun j => (e j).val, fun j => (e j).property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem giantSignedPromotionFamilyIntoFinsets_card {J : Type*} [Fintype J] [DecidableEq J]
    {n a : J → ℕ} (E : (j : J) → Finset (Fin (n j))) :
    Fintype.card {e : (j : J) → Fin (a j) ↪ Fin (n j) // ∀ j i, e j i ∈ E j} =
      ∏ j, (E j).card.descFactorial (a j) := by
  classical
  rw [Fintype.card_congr (giantSignedPromotionFamilyIntoFinsetsEquiv E), Fintype.card_pi]
  exact Finset.prod_congr rfl (fun j _ => giantSignedEmbeddingIntoFinset_card (E j))

theorem giantSignedPromotionFamilyIntoFinsets_sum {J : Type*} [Fintype J] [DecidableEq J]
    {n a : J → ℕ} (E : (j : J) → Finset (Fin (n j))) :
    (∑ e : (j : J) → Fin (a j) ↪ Fin (n j),
      if ∀ j i, e j i ∈ E j then (1 : ℝ) else 0) =
      ∏ j, ((E j).card.descFactorial (a j) : ℝ) := by
  classical
  have hc := giantSignedPromotionFamilyIntoFinsets_card (a := a) E
  rw [Fintype.card_subtype, Finset.card_filter] at hc
  exact_mod_cast hc

end
end ArtinMatthews
