module

public import ArtinMatthews.GiantSignedEdgeOrderedJoint
public import ArtinMatthews.GiantSignedEdgeRetrieval


set_option backward.privateInPublic true
@[expose] public section

/-! The factorial joint identity on the actual partial-injection carrier. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem giantSignedMemory_injection_joint_factorial
    {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)] {n a : J → ℕ}
    (μ : (j : J) → X j → ℂ)
    (H : ((j : J) → Fin (n j + a j) → X j) →
      ((j : J) → Fin (a j) → X j) → ((j : J) → Fin (n j) → X j) → ℂ)
    (hH : ∀ p u, MarkedRawGroupedTupleSymmetric (fun j => n j + a j)
      (fun old => H old p u)) :
    (∑ old : (j : J) → Fin (n j + a j) → X j,
      ((∏ j, ∏ i, μ j (old j i)) / (∏ j, (Nat.factorial (n j + a j) : ℂ))) *
        ∑ e : (j : J) → Fin (a j) ↪ Fin (n j + a j),
          H old (fun j => old j ∘ e j)
            (fun j => giantSignedRetrievalSurvivors (e j) (old j))) =
      ∑ p : (j : J) → Fin (a j) → X j,
        ∑ u : (j : J) → Fin (n j) → X j,
          ((∏ j, ∏ i, μ j (p j i)) * (∏ j, ∏ i, μ j (u j i))) /
            (∏ j, (Nat.factorial (n j) : ℂ)) *
            H (fun j => Fin.append (u j) (p j)) p u := by
  classical
  rw [← giantSignedMemory_ordered_joint_factorial μ H hH]
  apply Finset.sum_congr rfl
  intro old _
  congr 1
  rw [giantSignedPromotionFamily_sum]
  simp only [giantSignedPromotionEmbedding_retrieved, giantSignedPromotionEmbedding_survivors]

end
end ArtinMatthews
