module

public import ArtinMatthews.MarkedMinorArcRawGhostGroupedBatchAdjoint
public import ArtinMatthews.MarkedMinorArcRawGhostDegreeAdjoint


set_option backward.privateInPublic true
@[expose] public section

/-! Exact simultaneous signed ghost transpose for arbitrary coupled pending
functions.  Every old-index subset, repeated value, anchored ordered birth
and factorial is retained.  The source and target degrees can subsequently
be summed over their actual separate total-memory cutoffs. -/
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Literal signed ghost component at fixed groupwise survivor, deletion
and birth degrees. Charges can vary with the prime group. -/
noncomputable def markedRawGhostGroupedDegreeComponent
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset Nat.Primes) (ν : (j : J) → ↥(P j) → ℂ)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (n d l : J → ℕ) (δ γ s : J → ℂ)
    (f : ((j : J) → Fin (n j+l j) → MarkedRawParticle (P j)) → ℂ)
    (a : (j : J) → Fin (n j+d j) → MarkedRawParticle (P j)) : ℂ :=
  (∏ j,δ j^(d j)*γ j^(l j))*
    ∑ S : (j : J) → MarkedRawDeletionBatch (n j+d j) (d j),
      (∏ j,∏ i,if MarkedRawParticleHits (P j) z hz
        (markedRawDeletedTupleCast (S j).1 (markedRawDeletionBatch_deleted_card (S j)) (a j) i)
          then (1:ℂ) else 0)*
        (∏ j,s j^(markedRawTupleHitCount (P j) z hz
          (markedRawSurvivorTupleCast (S j).1 (markedRawDeletionBatch_survivor_card rfl (S j)) (a j))))*
        ∑ births : (j : J) → Fin (l j) → ↥(P j),
          ((∏ j,∏ i,ν j (births j i))/(∏ j,(Nat.factorial (l j) : ℂ)))*
            f (fun j => Fin.addCases
              (markedRawSurvivorTupleCast (S j).1 (markedRawDeletionBatch_survivor_card rfl (S j)) (a j))
              (markedRawAnchoredBatch (P j) z hz (l j) (births j)))

/-- Actual signed grouped ghost pairing reduced to its shared survivors.
The tests may couple all groups, and no root or probability hypothesis is
substituted for the true factorial measure. -/
theorem markedRawGhost_grouped_degree_pairing_survivors
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset Nat.Primes) (ν : (j : J) → ↥(P j) → ℂ)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (n d l : J → ℕ) (δ γ s : J → ℂ)
    (g : ((j : J) → Fin (n j+d j) → MarkedRawParticle (P j)) → ℂ)
    (hg : MarkedRawGroupedTupleSymmetric (fun j => n j+d j) g)
    (f : ((j : J) → Fin (n j+l j) → MarkedRawParticle (P j)) → ℂ) :
    (∑ a : (j : J) → Fin (n j+d j) → MarkedRawParticle (P j),
      ((∏ j,∏ i,ν j (a j i).1)/(∏ j,(Nat.factorial (n j+d j) : ℂ)))*g a*
        markedRawGhostGroupedDegreeComponent P ν z hz n d l δ γ s f a)=
      (∏ j,δ j^(d j)*γ j^(l j))*
        ∑ survivors : (j : J) → Fin (n j) → MarkedRawParticle (P j),
          ((∏ j,∏ i,ν j (survivors j i).1)/(∏ j,(Nat.factorial (n j) : ℂ)))*
            (∏ j,s j^(markedRawTupleHitCount (P j) z hz (survivors j)))*
            (∑ births : (j : J) → Fin (d j) → ↥(P j),
              ((∏ j,∏ i,ν j (births j i))/(∏ j,(Nat.factorial (d j) : ℂ)))*
                g (fun j => Fin.addCases (survivors j) (markedRawAnchoredBatch (P j) z hz (d j) (births j))))*
            (∑ births : (j : J) → Fin (l j) → ↥(P j),
              ((∏ j,∏ i,ν j (births j i))/(∏ j,(Nat.factorial (l j) : ℂ)))*
                f (fun j => Fin.addCases (survivors j) (markedRawAnchoredBatch (P j) z hz (l j) (births j)))) := by
  classical
  let F : ((j : J) → Fin (n j) → MarkedRawParticle (P j)) → ℂ := fun survivors =>
    (∏ j,s j^(markedRawTupleHitCount (P j) z hz (survivors j)))*
      ∑ births : (j : J) → Fin (l j) → ↥(P j),
        ((∏ j,∏ i,ν j (births j i))/(∏ j,(Nat.factorial (l j) : ℂ)))*
          f (fun j => Fin.addCases (survivors j) (markedRawAnchoredBatch (P j) z hz (l j) (births j)))
  have h := markedRawGhost_grouped_batch_delete_pairing P ν z hz (fun _ => rfl) g hg F
  calc
    _ = (∏ j,δ j^(d j)*γ j^(l j))*
        ∑ a : (j : J) → Fin (n j+d j) → MarkedRawParticle (P j),
          ((∏ j,∏ i,ν j (a j i).1)/(∏ j,(Nat.factorial (n j+d j) : ℂ)))*g a*
            ∑ S : (j : J) → MarkedRawDeletionBatch (n j+d j) (d j),
              (∏ j,∏ i,if MarkedRawParticleHits (P j) z hz
                (markedRawDeletedTupleCast (S j).1 (markedRawDeletionBatch_deleted_card (S j)) (a j) i)
                  then (1:ℂ) else 0)*
                F (fun j => markedRawSurvivorTupleCast (S j).1
                  (markedRawDeletionBatch_survivor_card rfl (S j)) (a j)) := by
      simp only [markedRawGhostGroupedDegreeComponent,F,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro S _
      apply Finset.sum_congr rfl
      intro births _
      ring
    _ = _ := by
      rw [h]
      congr 1
      apply Finset.sum_congr rfl
      intro survivors _
      dsimp only [F]
      simp only [Fin.cast_eq_self]
      ring

/-- Genuine full grouped fixed-degree signed transpose.  The true
surviving-hit factors are unchanged, and deletion/birth charges exchange
independently in each prime group. -/
theorem markedRawGhost_grouped_degree_transpose
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset Nat.Primes) (ν : (j : J) → ↥(P j) → ℂ)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (n d l : J → ℕ) (δ γ s : J → ℂ)
    (g : ((j : J) → Fin (n j+d j) → MarkedRawParticle (P j)) → ℂ)
    (hg : MarkedRawGroupedTupleSymmetric (fun j => n j+d j) g)
    (f : ((j : J) → Fin (n j+l j) → MarkedRawParticle (P j)) → ℂ)
    (hf : MarkedRawGroupedTupleSymmetric (fun j => n j+l j) f) :
    (∑ a : (j : J) → Fin (n j+d j) → MarkedRawParticle (P j),
      ((∏ j,∏ i,ν j (a j i).1)/(∏ j,(Nat.factorial (n j+d j) : ℂ)))*g a*
        markedRawGhostGroupedDegreeComponent P ν z hz n d l δ γ s f a)=
      ∑ b : (j : J) → Fin (n j+l j) → MarkedRawParticle (P j),
        ((∏ j,∏ i,ν j (b j i).1)/(∏ j,(Nat.factorial (n j+l j) : ℂ)))*f b*
          markedRawGhostGroupedDegreeComponent P ν z hz n l d γ δ s g b := by
  rw [markedRawGhost_grouped_degree_pairing_survivors P ν z hz n d l δ γ s g hg f,
    markedRawGhost_grouped_degree_pairing_survivors P ν z hz n l d γ δ s f hf g]
  have hc : (∏ j,γ j^(l j)*δ j^(d j))=∏ j,δ j^(d j)*γ j^(l j) :=
    Finset.prod_congr rfl (fun j _ => mul_comm _ _)
  rw [hc]
  congr 1
  apply Finset.sum_congr rfl
  intro survivors _
  ring

end ArtinMatthews
