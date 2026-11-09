module

public import ArtinMatthews.GiantSignedUniformBirthRank
public import ArtinMatthews.MarkedBirthMixedBudget


set_option backward.privateInPublic true
@[expose] public section

/-! The signed and absolute factors are counted on the actual affected
edge set of the common performed-birth frame. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

variable {B : Type*} [Fintype B] {M n R : ℕ}

def giantSignedUniformBirthModifiedEdges
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B M n R)) : Finset (Fin n) :=
  Finset.univ.filter (fun i =>
    GiantSignedBirthOperation.edge i ∈ σ.support.image (giantSignedUniformBirthOperation M n R))

theorem giantSignedUniformBirthModifiedEdges_mem
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B M n R)) (i : Fin n) :
    i ∈ giantSignedUniformBirthModifiedEdges σ ↔
      GiantSignedBirthOperation.edge i ∈ σ.support.image (giantSignedUniformBirthOperation M n R) := by
  simp [giantSignedUniformBirthModifiedEdges]

theorem giantSignedUniformBirthModifiedEdges_card
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B M n R)) :
    (giantSignedUniformBirthModifiedEdges σ).card ≤ 2 * markedBirthPermutationRank σ := by
  let edges := giantSignedUniformBirthModifiedEdges σ
  have hsub : edges.image GiantSignedBirthOperation.edge ⊆
      σ.support.image (giantSignedUniformBirthOperation M n R) := by
    intro o ho
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ho
    exact (giantSignedUniformBirthModifiedEdges_mem σ i).mp hi
  have hedge : Function.Injective (@GiantSignedBirthOperation.edge n) :=
    fun _ _ h => GiantSignedBirthOperation.edge.inj h
  calc
    _ = (edges.image GiantSignedBirthOperation.edge).card :=
      (Finset.card_image_of_injective edges hedge).symm
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := markedBirthPermutation_operations_le_twice_rank
      (giantSignedUniformBirthOperation M n R) σ

theorem giantSignedUniformBirth_edge_product {A : Type*} [CommMonoid A]
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B M n R)) (clean dirty : A) :
    let edges := giantSignedUniformBirthModifiedEdges σ
    (∏ i : Fin n, if i ∈ edges then dirty else clean) =
      clean^(n-edges.card) * dirty^edges.card := by
  let edges := giantSignedUniformBirthModifiedEdges σ
  change (∏ i : Fin n, if i ∈ edges then dirty else clean) = _
  have hyes : (Finset.univ.filter fun i => i ∈ edges) = edges := by ext i; simp
  have hno : (Finset.univ.filter fun i => i ∉ edges) = edgesᶜ := by ext i; simp
  rw [Finset.prod_ite, hyes, hno, Finset.prod_const, Finset.prod_const,
    Finset.card_compl, Fintype.card_fin, mul_comm]

theorem giantSignedUniformBirth_edge_norm_budget
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B M n R)) {a b : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 1 ≤ b)
    (hr : 2 * markedBirthPermutationRank σ ≤ n) :
    (∏ i : Fin n, if i ∈ giantSignedUniformBirthModifiedEdges σ then b else a) ≤
      a^(n-2*markedBirthPermutationRank σ) * b^(2*markedBirthPermutationRank σ) := by
  rw [giantSignedUniformBirth_edge_product]
  simpa only [max_eq_right hb] using markedMixedEdgeBudget_mono_count ha ha1 (zero_le_one.trans hb)
    (giantSignedUniformBirthModifiedEdges_card σ) hr

end
end ArtinMatthews
