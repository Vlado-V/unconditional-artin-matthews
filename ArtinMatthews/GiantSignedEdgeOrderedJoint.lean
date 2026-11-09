module

public import ArtinMatthews.GiantSignedEdgePermutation


set_option backward.privateInPublic true
@[expose] public section

/-! Ordered promotion indices cancel the retrieved-tuple factorial. The
survivors retain their literal ordered-list measure. -/

namespace ArtinMatthews
open scoped BigOperators
noncomputable section

section OrderedJoint
variable {J : Type*} [Fintype J] [DecidableEq J]
variable {X : J → Type*} [∀ j, Fintype (X j)] {n a : J → ℕ}

private theorem giantSignedOrderedJoint_fixed_permutation
    (μ : (j : J) → X j → ℂ)
    (H : ((j : J) → Fin (n j + a j) → X j) →
      ((j : J) → Fin (a j) → X j) → ((j : J) → Fin (n j) → X j) → ℂ)
    (hH : ∀ p u, MarkedRawGroupedTupleSymmetric (fun j => n j + a j)
      (fun old => H old p u))
    (σ : (j : J) → Equiv.Perm (Fin (a j))) :
    (∑ old : (j : J) → Fin (n j + a j) → X j,
      ((∏ j, ∏ i, μ j (old j i)) / (∏ j, (Nat.factorial (n j + a j) : ℂ))) *
        ∑ S : (j : J) → MarkedRawDeletionBatch (n j + a j) (a j),
          H old
            (fun j => markedRawDeletedTupleCast (S j).1
              (markedRawDeletionBatch_deleted_card (S j)) (old j) ∘ σ j)
            (fun j => markedRawSurvivorTupleCast (S j).1
              (markedRawDeletionBatch_survivor_card rfl (S j)) (old j))) =
      ∑ p : (j : J) → Fin (a j) → X j,
        ∑ u : (j : J) → Fin (n j) → X j,
          ((∏ j, ∏ i, μ j (p j i)) * (∏ j, ∏ i, μ j (u j i))) /
            ((∏ j, (Nat.factorial (a j) : ℂ)) * (∏ j, (Nat.factorial (n j) : ℂ))) *
            H (fun j => Fin.append (u j) (p j)) p u := by
  classical
  rw [markedRawMemory_grouped_joint_factorial (fun _ => rfl) μ
    (fun old p u => H old (fun j => p j ∘ σ j) u)
    (fun p u => hH (fun j => p j ∘ σ j) u)]
  let E := giantSignedGroupedTuplePermutation (X := X) σ
  calc
    _ = ∑ p : (j : J) → Fin (a j) → X j,
        ∑ u : (j : J) → Fin (n j) → X j,
          ((∏ j, ∏ i, μ j (E p j i)) * (∏ j, ∏ i, μ j (u j i))) /
            ((∏ j, (Nat.factorial (a j) : ℂ)) * (∏ j, (Nat.factorial (n j) : ℂ))) *
            H (fun j => Fin.append (u j) (E p j)) (E p) u := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro u _
      rw [giantSignedGroupedTuplePermutation_mass]
      congr 1
      exact (giantSignedGroupedTupleSymmetric_append_right
        (fun old => H old (E p) u) (hH (E p) u) u p σ).symm
    _ = _ := Equiv.sum_comp E (fun p =>
      ∑ u : (j : J) → Fin (n j) → X j,
        ((∏ j, ∏ i, μ j (p j i)) * (∏ j, ∏ i, μ j (u j i))) /
          ((∏ j, (Nat.factorial (a j) : ℂ)) * (∏ j, (Nat.factorial (n j) : ℂ))) *
          H (fun j => Fin.append (u j) (p j)) p u)

/-- Literal ordered retrievals remove exactly the promotion factorial.
The coupled test may depend on old, retrieved and surviving particles. -/
theorem giantSignedMemory_ordered_joint_factorial
    (μ : (j : J) → X j → ℂ)
    (H : ((j : J) → Fin (n j + a j) → X j) →
      ((j : J) → Fin (a j) → X j) → ((j : J) → Fin (n j) → X j) → ℂ)
    (hH : ∀ p u, MarkedRawGroupedTupleSymmetric (fun j => n j + a j)
      (fun old => H old p u)) :
    (∑ old : (j : J) → Fin (n j + a j) → X j,
      ((∏ j, ∏ i, μ j (old j i)) / (∏ j, (Nat.factorial (n j + a j) : ℂ))) *
        ∑ S : (j : J) → MarkedRawDeletionBatch (n j + a j) (a j),
          ∑ σ : (j : J) → Equiv.Perm (Fin (a j)),
            H old
              (fun j => markedRawDeletedTupleCast (S j).1
                (markedRawDeletionBatch_deleted_card (S j)) (old j) ∘ σ j)
              (fun j => markedRawSurvivorTupleCast (S j).1
                (markedRawDeletionBatch_survivor_card rfl (S j)) (old j))) =
      ∑ p : (j : J) → Fin (a j) → X j,
        ∑ u : (j : J) → Fin (n j) → X j,
          ((∏ j, ∏ i, μ j (p j i)) * (∏ j, ∏ i, μ j (u j i))) /
            (∏ j, (Nat.factorial (n j) : ℂ)) *
            H (fun j => Fin.append (u j) (p j)) p u := by
  classical
  have hcard : (Fintype.card ((j : J) → Equiv.Perm (Fin (a j))) : ℂ) =
      ∏ j, (Nat.factorial (a j) : ℂ) := by
    simp only [Fintype.card_pi, Fintype.card_perm, Fintype.card_fin, Nat.cast_prod]
  have hfa : (∏ j, (Nat.factorial (a j) : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun _ _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  have hfn : (∏ j, (Nat.factorial (n j) : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun _ _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  calc
    _ = ∑ σ : (j : J) → Equiv.Perm (Fin (a j)),
        ∑ old : (j : J) → Fin (n j + a j) → X j,
          ((∏ j, ∏ i, μ j (old j i)) / (∏ j, (Nat.factorial (n j + a j) : ℂ))) *
            ∑ S : (j : J) → MarkedRawDeletionBatch (n j + a j) (a j),
              H old
                (fun j => markedRawDeletedTupleCast (S j).1
                  (markedRawDeletionBatch_deleted_card (S j)) (old j) ∘ σ j)
                (fun j => markedRawSurvivorTupleCast (S j).1
                  (markedRawDeletionBatch_survivor_card rfl (S j)) (old j)) := by
      simp only [Finset.mul_sum]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro old _
      exact Finset.sum_comm
    _ = ∑ _σ : (j : J) → Equiv.Perm (Fin (a j)),
        ∑ p : (j : J) → Fin (a j) → X j,
          ∑ u : (j : J) → Fin (n j) → X j,
            ((∏ j, ∏ i, μ j (p j i)) * (∏ j, ∏ i, μ j (u j i))) /
              ((∏ j, (Nat.factorial (a j) : ℂ)) * (∏ j, (Nat.factorial (n j) : ℂ))) *
              H (fun j => Fin.append (u j) (p j)) p u := by
      apply Finset.sum_congr rfl
      intro σ _
      exact giantSignedOrderedJoint_fixed_permutation μ H hH σ
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      field_simp [hfa, hfn]
end OrderedJoint

end
end ArtinMatthews
