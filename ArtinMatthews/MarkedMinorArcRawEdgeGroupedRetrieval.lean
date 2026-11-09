module

public import ArtinMatthews.MarkedMinorArcRawMemoryGroupedFactorial
public import ArtinMatthews.MarkedMinorArcRawMemoryGroupedAnchors


set_option backward.privateInPublic true
@[expose] public section

/-! Actual simultaneous indexed retrieval integration with a test jointly
depending on all retrieved primes and all surviving particles. This is
the factorial step for the store/promote edge transpose; prescribed edge
slots use deleted degree zero or one in each group. -/
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Genuine grouped retrieval formula.  Both the selected prime values
and the surviving memory are retained in the coupled test, and the hit
condition forces exactly the current anchor for each retrieved prime. -/
theorem markedRawEdge_grouped_retrieval_pairing
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset Nat.Primes) (ν : (j : J) → ↥(P j) → ℂ)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) {k n d : J → ℕ}
    (hk : ∀ j,n j+d j=k j)
    (g : ((j : J) → Fin (k j) → MarkedRawParticle (P j)) → ℂ)
    (hg : MarkedRawGroupedTupleSymmetric k g)
    (F : ((j : J) → Fin (d j) → ↥(P j)) →
      ((j : J) → Fin (n j) → MarkedRawParticle (P j)) → ℂ) :
    (∑ a : (j : J) → Fin (k j) → MarkedRawParticle (P j),
      ((∏ j,∏ i,ν j (a j i).1)/(∏ j,(Nat.factorial (k j) : ℂ)))*g a*
        ∑ S : (j : J) → MarkedRawDeletionBatch (k j) (d j),
          (∏ j,∏ i,if MarkedRawParticleHits (P j) z hz
            (markedRawDeletedTupleCast (S j).1 (markedRawDeletionBatch_deleted_card (S j)) (a j) i)
              then (1:ℂ) else 0)*
            F (fun j i => (markedRawDeletedTupleCast (S j).1 (markedRawDeletionBatch_deleted_card (S j)) (a j) i).1)
              (fun j => markedRawSurvivorTupleCast (S j).1
                (markedRawDeletionBatch_survivor_card (hk j) (S j)) (a j)))=
      ∑ survivors : (j : J) → Fin (n j) → MarkedRawParticle (P j),
        ((∏ j,∏ i,ν j (survivors j i).1)/(∏ j,(Nat.factorial (n j) : ℂ)))*
          ∑ retrieved : (j : J) → Fin (d j) → ↥(P j),
            ((∏ j,∏ i,ν j (retrieved j i))/(∏ j,(Nat.factorial (d j) : ℂ)))*
              g (fun j i => Fin.addCases (survivors j)
                (markedRawAnchoredBatch (P j) z hz (d j) (retrieved j)) (Fin.cast (hk j).symm i))*
              F retrieved survivors := by
  classical
  have hn : (∏ j,(Nat.factorial (n j) : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  have hd : (∏ j,(Nat.factorial (d j) : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  have h := markedRawMemory_grouped_factorial_batch_delete hk
    (fun j (a : MarkedRawParticle (P j)) => ν j a.1) g hg
    (fun deleted survivors =>
      (∏ j,∏ i,if MarkedRawParticleHits (P j) z hz (deleted j i) then (1:ℂ) else 0)*
        F (fun j i => (deleted j i).1) survivors)
  rw [h,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro survivors _
  calc
    _ = ((∏ j,∏ i,ν j (survivors j i).1)/(∏ j,(Nat.factorial (n j) : ℂ)))*
        ((∑ deleted : (j : J) → Fin (d j) → MarkedRawParticle (P j),
          (∏ j,∏ i,ν j (deleted j i).1)*
            (∏ j,∏ i,if MarkedRawParticleHits (P j) z hz (deleted j i) then (1:ℂ) else 0)*
            (g (fun j i => Fin.addCases (survivors j) (deleted j) (Fin.cast (hk j).symm i))*
              F (fun j i => (deleted j i).1) survivors))/
              (∏ j,(Nat.factorial (d j) : ℂ))) := by
      rw [Finset.sum_div,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro deleted _
      field_simp
    _ = _ := by
      rw [markedRawParticle_grouped_batch_hit_integral P ν z hz d
        (fun deleted =>
          g (fun j i => Fin.addCases (survivors j) (deleted j) (Fin.cast (hk j).symm i))*
            F (fun j i => (deleted j i).1) survivors)]
      simp only [Finset.sum_div,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro retrieved _
      have hprime : (fun j i => (markedRawAnchoredBatch (P j) z hz (d j) (retrieved j) i).1)=retrieved := rfl
      rw [hprime]
      ring

end ArtinMatthews
