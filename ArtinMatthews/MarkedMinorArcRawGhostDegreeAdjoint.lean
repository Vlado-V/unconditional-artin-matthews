module

public import ArtinMatthews.MarkedMinorArcRawGhostBatchAdjoint


set_option backward.privateInPublic true
@[expose] public section

/-! Exact signed ghost adjunction at fixed survivor, deletion and birth
degrees.  This is the actual unordered old-index sum and ordered anchored
birth sum with their factorial measures.  Repeated particle values are
retained throughout. -/
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The surviving indexed particles that hit the actual current line. -/
noncomputable def markedRawTupleHitCount (P : Finset Nat.Primes)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) {n : ℕ}
    (a : Fin n → MarkedRawParticle P) : ℕ :=
  (Finset.univ.filter (fun i => MarkedRawParticleHits P z hz (a i))).card

/-- Literal fixed-degree signed ghost action: delete an eligible unordered
old batch, apply the surviving-hit factor, and append ordered anchored
births with their true reciprocal factorial. -/
noncomputable def markedRawGhostDegreeComponent (P : Finset Nat.Primes)
    (ν : P → ℂ) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (n d l : ℕ) (δ γ s : ℂ) (f : (Fin (n+l) → MarkedRawParticle P) → ℂ)
    (a : Fin (n+d) → MarkedRawParticle P) : ℂ :=
  δ^d*γ^l*∑ S : MarkedRawDeletionBatch (n+d) d,
    (∏ i, if MarkedRawParticleHits P z hz
      (markedRawDeletedTupleCast S.1 (markedRawDeletionBatch_deleted_card S) a i) then (1:ℂ) else 0)*
      s^(markedRawTupleHitCount P z hz
        (markedRawSurvivorTupleCast S.1 (markedRawDeletionBatch_survivor_card rfl S) a))*
      ∑ births : Fin l → P, ((∏ i,ν (births i))/(Nat.factorial l : ℂ))*
        f (Fin.addCases
          (markedRawSurvivorTupleCast S.1 (markedRawDeletionBatch_survivor_card rfl S) a)
          (markedRawAnchoredBatch P z hz l births))

/-- Exact central-survivor formula for the true fixed-degree ghost rule.
The source symmetry is the only reason its unordered old batches may be
replaced by an anchored birth integral. -/
theorem markedRawGhost_degree_pairing_survivors (P : Finset Nat.Primes)
    (ν : P → ℂ) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (n d l : ℕ) (δ γ s : ℂ)
    (g : (Fin (n+d) → MarkedRawParticle P) → ℂ)
    (hg : MarkedRawTupleSymmetric (n+d) g)
    (f : (Fin (n+l) → MarkedRawParticle P) → ℂ) :
    (∑ a : Fin (n+d) → MarkedRawParticle P,
      ((∏ i,ν (a i).1)/(Nat.factorial (n+d) : ℂ))*g a*
        markedRawGhostDegreeComponent P ν z hz n d l δ γ s f a)=
      δ^d*γ^l*∑ survivors : Fin n → MarkedRawParticle P,
        ((∏ i,ν (survivors i).1)/(Nat.factorial n : ℂ))*
          s^(markedRawTupleHitCount P z hz survivors)*
          (∑ births : Fin d → P, ((∏ i,ν (births i))/(Nat.factorial d : ℂ))*
            g (Fin.addCases survivors (markedRawAnchoredBatch P z hz d births)))*
          (∑ births : Fin l → P, ((∏ i,ν (births i))/(Nat.factorial l : ℂ))*
            f (Fin.addCases survivors (markedRawAnchoredBatch P z hz l births))) := by
  classical
  let F : (Fin n → MarkedRawParticle P) → ℂ := fun survivors =>
    s^(markedRawTupleHitCount P z hz survivors)*
      ∑ births : Fin l → P, ((∏ i,ν (births i))/(Nat.factorial l : ℂ))*
        f (Fin.addCases survivors (markedRawAnchoredBatch P z hz l births))
  have h := markedRawGhost_batch_delete_pairing P ν z hz n d g hg F
  calc
    _ = δ^d*γ^l*∑ a : Fin (n+d) → MarkedRawParticle P,
        ((∏ i,ν (a i).1)/(Nat.factorial (n+d) : ℂ))*g a*
          ∑ S : MarkedRawDeletionBatch (n+d) d,
            (∏ i, if MarkedRawParticleHits P z hz
              (markedRawDeletedTupleCast S.1 (markedRawDeletionBatch_deleted_card S) a i) then (1:ℂ) else 0)*
              F (markedRawSurvivorTupleCast S.1 (markedRawDeletionBatch_survivor_card rfl S) a) := by
      simp only [markedRawGhostDegreeComponent,F,Finset.mul_sum]
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
      ring

/-- Genuine signed fixed-degree transpose.  Deletion and birth degrees,
and their charges, are exchanged; the actual surviving-hit weight is
unchanged.  Both pending functions must have the source's true index
symmetry. -/
theorem markedRawGhost_degree_transpose (P : Finset Nat.Primes)
    (ν : P → ℂ) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (n d l : ℕ) (δ γ s : ℂ)
    (g : (Fin (n+d) → MarkedRawParticle P) → ℂ)
    (hg : MarkedRawTupleSymmetric (n+d) g)
    (f : (Fin (n+l) → MarkedRawParticle P) → ℂ)
    (hf : MarkedRawTupleSymmetric (n+l) f) :
    (∑ a : Fin (n+d) → MarkedRawParticle P,
      ((∏ i,ν (a i).1)/(Nat.factorial (n+d) : ℂ))*g a*
        markedRawGhostDegreeComponent P ν z hz n d l δ γ s f a)=
      ∑ b : Fin (n+l) → MarkedRawParticle P,
        ((∏ i,ν (b i).1)/(Nat.factorial (n+l) : ℂ))*f b*
          markedRawGhostDegreeComponent P ν z hz n l d γ δ s g b := by
  rw [markedRawGhost_degree_pairing_survivors P ν z hz n d l δ γ s g hg f,
    markedRawGhost_degree_pairing_survivors P ν z hz n l d γ δ s f hf g]
  rw [show γ^l*δ^d=δ^d*γ^l by ring]
  congr 1
  apply Finset.sum_congr rfl
  intro survivors _
  ring

end ArtinMatthews
