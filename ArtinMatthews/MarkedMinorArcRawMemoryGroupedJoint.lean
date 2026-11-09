module

public import ArtinMatthews.MarkedMinorArcRawMemoryGroupedFactorial


set_option backward.privateInPublic true
@[expose] public section

/-! Actual factorial integration for kernels depending jointly on the old
pending memory, the retrieved particles and the survivors.  This removes
no joint endpoint restriction: only the literal old-index permutation
invariance required by the physical kernel is used. -/
namespace ArtinMatthews
open scoped BigOperators

/-- The true old tuple and its survivor-then-retrieved reassembly have the
same value under any independently symmetric old-memory test. -/
theorem markedRawGroupedTupleSymmetric_reassemble
    {J : Type*} {X : J → Type*} {k n d : J → ℕ}
    (hk : ∀ j,n j+d j=k j)
    (S : (j : J) → MarkedRawDeletionBatch (k j) (d j))
    (a : (j : J) → Fin (k j) → X j)
    (g : ((j : J) → Fin (k j) → X j) → ℂ) (hg : MarkedRawGroupedTupleSymmetric k g) :
    g a=g (fun j i => Fin.addCases
      (markedRawSurvivorTupleCast (S j).1 (markedRawDeletionBatch_survivor_card (hk j) (S j)) (a j))
      (markedRawDeletedTupleCast (S j).1 (markedRawDeletionBatch_deleted_card (S j)) (a j))
      (Fin.cast (hk j).symm i)) := by
  let c : (j : J) → Fin (k j) → X j := fun j i => Fin.addCases
    (markedRawSurvivorTupleCast (S j).1 (markedRawDeletionBatch_survivor_card (hk j) (S j)) (a j))
    (markedRawDeletedTupleCast (S j).1 (markedRawDeletionBatch_deleted_card (S j)) (a j))
    (Fin.cast (hk j).symm i)
  have ha : a=fun j => c j ∘ markedRawSubsetReassemblyPerm (S j).1 := by
    funext j
    let E := markedRawSubsetFixedTupleEquiv (X := X j) (S j).1
      (markedRawDeletionBatch_deleted_card (S j)) (markedRawDeletionBatch_survivor_card (hk j) (S j))
    have h := E.symm_apply_apply (a j)
    change (markedRawSubsetFixedTupleEquiv (S j).1
      (markedRawDeletionBatch_deleted_card (S j)) (markedRawDeletionBatch_survivor_card (hk j) (S j))).symm
        (markedRawSubsetFixedTupleEquiv (S j).1
          (markedRawDeletionBatch_deleted_card (S j)) (markedRawDeletionBatch_survivor_card (hk j) (S j)) (a j))=a j at h
    rw [markedRawSubsetFixedTupleEquiv_apply,markedRawSubsetFixedTupleEquiv_inverse (hk j)] at h
    exact h.symm
  exact (congrArg g ha).trans (hg c (fun j => markedRawSubsetReassemblyPerm (S j).1))

/-- Exact grouped unordered-index factorial formula for a genuinely joint
kernel. The old-memory symmetry is required separately for each fixed
retrieved and surviving tuple; no factorization of the kernel is assumed. -/
theorem markedRawMemory_grouped_joint_factorial
    {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀ j,Fintype (X j)] {k n d : J → ℕ}
    (hk : ∀ j,n j+d j=k j) (μ : (j : J) → X j → ℂ)
    (H : ((j : J) → Fin (k j) → X j) → ((j : J) → Fin (d j) → X j) →
      ((j : J) → Fin (n j) → X j) → ℂ)
    (hH : ∀ deleted survivors,MarkedRawGroupedTupleSymmetric k (fun old => H old deleted survivors)) :
    (∑ old : (j : J) → Fin (k j) → X j,
      ((∏ j,∏ i,μ j (old j i))/(∏ j,(Nat.factorial (k j) : ℂ)))*
        ∑ S : (j : J) → MarkedRawDeletionBatch (k j) (d j),
          H old
            (fun j => markedRawDeletedTupleCast (S j).1 (markedRawDeletionBatch_deleted_card (S j)) (old j))
            (fun j => markedRawSurvivorTupleCast (S j).1
              (markedRawDeletionBatch_survivor_card (hk j) (S j)) (old j)))=
      ∑ deleted : (j : J) → Fin (d j) → X j,
        ∑ survivors : (j : J) → Fin (n j) → X j,
          ((∏ j,∏ i,μ j (deleted j i))*(∏ j,∏ i,μ j (survivors j i)))/
            ((∏ j,(Nat.factorial (d j) : ℂ))*(∏ j,(Nat.factorial (n j) : ℂ)))*
            H (fun j i => Fin.addCases (survivors j) (deleted j) (Fin.cast (hk j).symm i))
              deleted survivors := by
  classical
  let F := fun deleted survivors =>
    H (fun j i => Fin.addCases (survivors j) (deleted j) (Fin.cast (hk j).symm i)) deleted survivors
  have h := markedRawMemory_grouped_factorial_batch_delete hk μ (fun _ => (1:ℂ))
    (fun _ _ => rfl) F
  simp only [mul_one] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro old _
  congr 1
  apply Finset.sum_congr rfl
  intro S _
  exact markedRawGroupedTupleSymmetric_reassemble hk S old _
    (hH (fun j => markedRawDeletedTupleCast (S j).1 (markedRawDeletionBatch_deleted_card (S j)) (old j))
      (fun j => markedRawSurvivorTupleCast (S j).1
        (markedRawDeletionBatch_survivor_card (hk j) (S j)) (old j)))

end ArtinMatthews
