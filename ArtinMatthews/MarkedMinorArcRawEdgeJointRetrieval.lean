module

public import ArtinMatthews.MarkedMinorArcRawMemoryGroupedJoint
public import ArtinMatthews.MarkedMinorArcRawMemoryGroupedAnchors


set_option backward.privateInPublic true
@[expose] public section

/-! Exact anchored retrieval integration for a joint edge kernel.  The
kernel may couple the old memory, retrieved prime labels and surviving
memory; all physical joint endpoint restrictions may therefore remain
inside it. -/
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedRawEdge_joint_retrieval_pairing
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset Nat.Primes) (ν : (j : J) → ↥(P j) → ℂ)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) {k n d : J → ℕ}
    (hk : ∀ j,n j+d j=k j)
    (H : ((j : J) → Fin (k j) → MarkedRawParticle (P j)) →
      ((j : J) → Fin (d j) → ↥(P j)) →
      ((j : J) → Fin (n j) → MarkedRawParticle (P j)) → ℂ)
    (hH : ∀ retrieved survivors,MarkedRawGroupedTupleSymmetric k
      (fun old => H old retrieved survivors)) :
    (∑ old : (j : J) → Fin (k j) → MarkedRawParticle (P j),
      ((∏ j,∏ i,ν j (old j i).1)/(∏ j,(Nat.factorial (k j) : ℂ)))*
        ∑ S : (j : J) → MarkedRawDeletionBatch (k j) (d j),
          (∏ j,∏ i,if MarkedRawParticleHits (P j) z hz
            (markedRawDeletedTupleCast (S j).1 (markedRawDeletionBatch_deleted_card (S j)) (old j) i)
              then (1:ℂ) else 0)*
            H old (fun j i => (markedRawDeletedTupleCast (S j).1
              (markedRawDeletionBatch_deleted_card (S j)) (old j) i).1)
              (fun j => markedRawSurvivorTupleCast (S j).1
                (markedRawDeletionBatch_survivor_card (hk j) (S j)) (old j)))=
      ∑ survivors : (j : J) → Fin (n j) → MarkedRawParticle (P j),
        ((∏ j,∏ i,ν j (survivors j i).1)/(∏ j,(Nat.factorial (n j) : ℂ)))*
          ∑ retrieved : (j : J) → Fin (d j) → ↥(P j),
            ((∏ j,∏ i,ν j (retrieved j i))/(∏ j,(Nat.factorial (d j) : ℂ)))*
              H (fun j i => Fin.addCases (survivors j)
                (markedRawAnchoredBatch (P j) z hz (d j) (retrieved j)) (Fin.cast (hk j).symm i))
                retrieved survivors := by
  classical
  have hn : (∏ j,(Nat.factorial (n j) : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  have hd : (∏ j,(Nat.factorial (d j) : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  have h := markedRawMemory_grouped_joint_factorial hk
    (fun j (a : MarkedRawParticle (P j)) => ν j a.1)
    (fun old deleted survivors =>
      (∏ j,∏ i,if MarkedRawParticleHits (P j) z hz (deleted j i) then (1:ℂ) else 0)*
        H old (fun j i => (deleted j i).1) survivors)
    (by
      intro deleted survivors old σ
      dsimp only
      congr 1
      exact hH _ _ old σ)
  rw [h,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro survivors _
  calc
    _ = ((∏ j,∏ i,ν j (survivors j i).1)/(∏ j,(Nat.factorial (n j) : ℂ)))*
        ((∑ deleted : (j : J) → Fin (d j) → MarkedRawParticle (P j),
          (∏ j,∏ i,ν j (deleted j i).1)*
            (∏ j,∏ i,if MarkedRawParticleHits (P j) z hz (deleted j i) then (1:ℂ) else 0)*
            H (fun j i => Fin.addCases (survivors j) (deleted j) (Fin.cast (hk j).symm i))
              (fun j i => (deleted j i).1) survivors)/(∏ j,(Nat.factorial (d j) : ℂ))) := by
      rw [Finset.sum_div,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro deleted _
      field_simp
    _ = _ := by
      rw [markedRawParticle_grouped_batch_hit_integral P ν z hz d
        (fun deleted => H (fun j i => Fin.addCases (survivors j) (deleted j) (Fin.cast (hk j).symm i))
          (fun j i => (deleted j i).1) survivors)]
      simp only [Finset.sum_div,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro retrieved _
      have hprime : (fun j i => (markedRawAnchoredBatch (P j) z hz (d j) (retrieved j) i).1)=retrieved := rfl
      rw [hprime]
      ring

end ArtinMatthews
