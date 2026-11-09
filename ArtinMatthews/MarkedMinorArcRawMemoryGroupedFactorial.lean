module

public import ArtinMatthews.MarkedMinorArcRawMemoryGroupedSubset


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine simultaneous unordered-batch factorial integration.  The tests
may couple all prime groups; the factor `1/(d_j! n_j!)` is derived from
the cardinality of their actual indexed deletion-subset families. -/
namespace ArtinMatthews
open scoped BigOperators

/-- Tensor factorial deletion formula with arbitrary coupled symmetric
pending tests and every repeated particle value retained. -/
theorem markedRawMemory_grouped_factorial_batch_delete
    {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀ j,Fintype (X j)] {k n d : J → ℕ}
    (hk : ∀ j,n j+d j=k j) (μ : (j : J) → X j → ℂ)
    (g : ((j : J) → Fin (k j) → X j) → ℂ) (hg : MarkedRawGroupedTupleSymmetric k g)
    (f : ((j : J) → Fin (d j) → X j) → ((j : J) → Fin (n j) → X j) → ℂ) :
    (∑ a : (j : J) → Fin (k j) → X j,
      ((∏ j,∏ i,μ j (a j i))/(∏ j,(Nat.factorial (k j) : ℂ)))*g a*
        ∑ S : (j : J) → MarkedRawDeletionBatch (k j) (d j),
          f (fun j => markedRawDeletedTupleCast (S j).1 (markedRawDeletionBatch_deleted_card (S j)) (a j))
            (fun j => markedRawSurvivorTupleCast (S j).1
              (markedRawDeletionBatch_survivor_card (hk j) (S j)) (a j)))=
      ∑ deleted : (j : J) → Fin (d j) → X j,
        ∑ survivors : (j : J) → Fin (n j) → X j,
          ((∏ j,∏ i,μ j (deleted j i))*(∏ j,∏ i,μ j (survivors j i)))/
            ((∏ j,(Nat.factorial (d j) : ℂ))*(∏ j,(Nat.factorial (n j) : ℂ)))*
            g (fun j i => Fin.addCases (survivors j) (deleted j) (Fin.cast (hk j).symm i))*
              f deleted survivors := by
  classical
  let R : ℂ := ∑ deleted : (j : J) → Fin (d j) → X j,
    ∑ survivors : (j : J) → Fin (n j) → X j,
      (∏ j,∏ i,μ j (deleted j i))*(∏ j,∏ i,μ j (survivors j i))*
        g (fun j i => Fin.addCases (survivors j) (deleted j) (Fin.cast (hk j).symm i))*
          f deleted survivors
  have hfac (j : J) : ((k j).choose (d j) : ℂ)*(Nat.factorial (d j) : ℂ)*
      (Nat.factorial (n j) : ℂ)=(Nat.factorial (k j) : ℂ) := by
    have hd : d j ≤ k j := by have := hk j; omega
    have hn : k j-d j=n j := by have := hk j; omega
    have h := Nat.choose_mul_factorial_mul_factorial hd
    rw [hn] at h
    exact_mod_cast h
  have hfacAll : (∏ j,((k j).choose (d j) : ℂ))*(∏ j,(Nat.factorial (d j) : ℂ))*
      (∏ j,(Nat.factorial (n j) : ℂ))=∏ j,(Nat.factorial (k j) : ℂ) := by
    rw [← Finset.prod_mul_distrib,← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun j _ => hfac j)
  have hcard : (Fintype.card ((j : J) → MarkedRawDeletionBatch (k j) (d j)) : ℂ)=
      ∏ j,((k j).choose (d j) : ℂ) := by
    simp only [Fintype.card_pi,markedRawDeletionBatch_card,Nat.cast_prod]
  have hfk : (∏ j,(Nat.factorial (k j) : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  have hfd : (∏ j,(Nat.factorial (d j) : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  have hfn : (∏ j,(Nat.factorial (n j) : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  calc
    _ = ∑ S : (j : J) → MarkedRawDeletionBatch (k j) (d j),
        (∑ a : (j : J) → Fin (k j) → X j, (∏ j,∏ i,μ j (a j i))*g a*
          f (fun j => markedRawDeletedTupleCast (S j).1 (markedRawDeletionBatch_deleted_card (S j)) (a j))
            (fun j => markedRawSurvivorTupleCast (S j).1
              (markedRawDeletionBatch_survivor_card (hk j) (S j)) (a j)))/
          (∏ j,(Nat.factorial (k j) : ℂ)) := by
      simp only [div_eq_mul_inv,Finset.mul_sum,Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro S _
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = ∑ _S : (j : J) → MarkedRawDeletionBatch (k j) (d j),
        R/(∏ j,(Nat.factorial (k j) : ℂ)) := by
      apply Finset.sum_congr rfl
      intro S _
      rw [markedRawMemory_grouped_subset_integral hk (fun j => (S j).1)
        (fun j => markedRawDeletionBatch_deleted_card (S j))
        (fun j => markedRawDeletionBatch_survivor_card (hk j) (S j)) μ g hg f]
    _ = (∏ j,((k j).choose (d j) : ℂ))*R/(∏ j,(Nat.factorial (k j) : ℂ)) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hcard]
      ring
    _ = R/((∏ j,(Nat.factorial (d j) : ℂ))*(∏ j,(Nat.factorial (n j) : ℂ))) := by
      apply (div_eq_div_iff hfk (mul_ne_zero hfd hfn)).mpr
      linear_combination R*hfacAll
    _ = _ := by
      dsimp only [R]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro deleted _
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro survivors _
      ring

end ArtinMatthews
