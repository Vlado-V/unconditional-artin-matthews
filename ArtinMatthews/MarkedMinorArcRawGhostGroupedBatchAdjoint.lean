module

public import ArtinMatthews.MarkedMinorArcRawMemoryGroupedFactorial
public import ArtinMatthews.MarkedMinorArcRawMemoryGroupedAnchors


set_option backward.privateInPublic true
@[expose] public section

/-! The true factorial ghost deletion/anchored-birth pairing for all prime
groups at once. Arbitrary coupled pending functions are allowed, subject
only to their actual independent old-index permutation symmetry. -/
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Actual simultaneous unordered deletion/anchored creation integration.
The factorial product is obtained from actual finite indexed choices. -/
theorem markedRawGhost_grouped_batch_delete_pairing
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset Nat.Primes) (ν : (j : J) → ↥(P j) → ℂ)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) {k n d : J → ℕ}
    (hk : ∀ j,n j+d j=k j)
    (g : ((j : J) → Fin (k j) → MarkedRawParticle (P j)) → ℂ)
    (hg : MarkedRawGroupedTupleSymmetric k g)
    (f : ((j : J) → Fin (n j) → MarkedRawParticle (P j)) → ℂ) :
    (∑ a : (j : J) → Fin (k j) → MarkedRawParticle (P j),
      ((∏ j,∏ i,ν j (a j i).1)/(∏ j,(Nat.factorial (k j) : ℂ)))*g a*
        ∑ S : (j : J) → MarkedRawDeletionBatch (k j) (d j),
          (∏ j,∏ i,if MarkedRawParticleHits (P j) z hz
            (markedRawDeletedTupleCast (S j).1 (markedRawDeletionBatch_deleted_card (S j)) (a j) i)
              then (1:ℂ) else 0)*
            f (fun j => markedRawSurvivorTupleCast (S j).1
              (markedRawDeletionBatch_survivor_card (hk j) (S j)) (a j)))=
      ∑ survivors : (j : J) → Fin (n j) → MarkedRawParticle (P j),
        ((∏ j,∏ i,ν j (survivors j i).1)/(∏ j,(Nat.factorial (n j) : ℂ)))*f survivors*
          ∑ births : (j : J) → Fin (d j) → ↥(P j),
            ((∏ j,∏ i,ν j (births j i))/(∏ j,(Nat.factorial (d j) : ℂ)))*
              g (fun j i => Fin.addCases (survivors j)
                (markedRawAnchoredBatch (P j) z hz (d j) (births j)) (Fin.cast (hk j).symm i)) := by
  classical
  have hn : (∏ j,(Nat.factorial (n j) : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  have hd : (∏ j,(Nat.factorial (d j) : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  have h := markedRawMemory_grouped_factorial_batch_delete hk
    (fun j (a : MarkedRawParticle (P j)) => ν j a.1) g hg
    (fun deleted survivors =>
      (∏ j,∏ i,if MarkedRawParticleHits (P j) z hz (deleted j i) then (1:ℂ) else 0)*f survivors)
  rw [h,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro survivors _
  calc
    _ = ((∏ j,∏ i,ν j (survivors j i).1)/(∏ j,(Nat.factorial (n j) : ℂ)))*f survivors*
        ((∑ deleted : (j : J) → Fin (d j) → MarkedRawParticle (P j),
          (∏ j,∏ i,ν j (deleted j i).1)*
            (∏ j,∏ i,if MarkedRawParticleHits (P j) z hz (deleted j i) then (1:ℂ) else 0)*
            g (fun j i => Fin.addCases (survivors j) (deleted j) (Fin.cast (hk j).symm i)))/
              (∏ j,(Nat.factorial (d j) : ℂ))) := by
      rw [Finset.sum_div,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro deleted _
      field_simp
    _ = _ := by
      rw [markedRawParticle_grouped_batch_hit_integral P ν z hz d
        (fun deleted => g (fun j i => Fin.addCases (survivors j) (deleted j) (Fin.cast (hk j).symm i)))]
      simp only [Finset.sum_div,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro births _
      ring

end ArtinMatthews
