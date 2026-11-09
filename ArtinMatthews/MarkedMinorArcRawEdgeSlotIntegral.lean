module

public import ArtinMatthews.MarkedMinorArcRawEdgeJointRetrieval


set_option backward.privateInPublic true
@[expose] public section

/-! Literal zero-or-one promotion integration.  Constraining each promoted
old prime to the actual target slot completes exactly one full tilted target
draw, including atoms of weight zero.  The coupled kernel retains both the
old memory and its survivors throughout the factorial integration. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Only unpromoted groups receive a fresh target-prime factor. -/
def markedRawEdgeFreePrimeMass {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℂ)
    (d : J → ℕ) (b : (j : J) → ↥(P j)) : ℂ :=
  ∏ j, if d j = 0 then ν j (b j) else 1

/-- The deleted old labels must agree with the actual target active slots. -/
def MarkedRawEdgeRetrievedSlots {J : Type*} {P : J → Finset Nat.Primes}
    {d : J → ℕ} (retrieved : (j : J) → Fin (d j) → ↥(P j))
    (b : (j : J) → ↥(P j)) : Prop := ∀ j i, retrieved j i = b j

theorem markedRawEdgeRetrievedSlots_iff {J : Type*} {P : J → Finset Nat.Primes}
    {d : J → ℕ} (retrieved : (j : J) → Fin (d j) → ↥(P j))
    (b : (j : J) → ↥(P j)) :
    MarkedRawEdgeRetrievedSlots retrieved b ↔ retrieved = fun j _ => b j := by
  constructor
  · intro h
    exact funext (fun j => funext (h j))
  · intro h
    subst retrieved
    exact fun _ _ => rfl

/-- A promoted coordinate's old atom and an unpromoted coordinate's fresh
atom form the same complete target atom, without dividing by any atom. -/
theorem markedRawEdge_retrieved_slots_mass {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℂ)
    (d : J → ℕ) (hd : ∀ j, d j ≤ 1) (b : (j : J) → ↥(P j)) :
    ((∏ j, ∏ _i : Fin (d j), ν j (b j)) /
      (∏ j, (Nat.factorial (d j) : ℂ))) * markedRawEdgeFreePrimeMass ν d b =
      ∏ j, ν j (b j) := by
  unfold markedRawEdgeFreePrimeMass
  rw [← Finset.prod_div_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hd j) with h | h <;> simp [h]

/-- Fixed-degree, full-slot promotion formula.  The target label is kept
inside the genuinely joint endpoint kernel.  Every selected old index and
the complete survivor tuple are retained, and the target mass is derived. -/
theorem markedRawEdge_slot_integral
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset Nat.Primes) (ν : (j : J) → ↥(P j) → ℂ)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) {k n d : J → ℕ}
    (hk : ∀ j, n j + d j = k j) (hd : ∀ j, d j ≤ 1)
    (H : ((j : J) → Fin (k j) → MarkedRawParticle (P j)) →
      ((j : J) → ↥(P j)) →
      ((j : J) → Fin (n j) → MarkedRawParticle (P j)) → ℂ)
    (hH : ∀ b survivors, MarkedRawGroupedTupleSymmetric k
      (fun old => H old b survivors)) :
    (∑ old : (j : J) → Fin (k j) → MarkedRawParticle (P j),
      ((∏ j, ∏ i, ν j (old j i).1) / (∏ j, (Nat.factorial (k j) : ℂ))) *
        ∑ S : (j : J) → MarkedRawDeletionBatch (k j) (d j),
          (∏ j, ∏ i, if MarkedRawParticleHits (P j) z hz
            (markedRawDeletedTupleCast (S j).1
              (markedRawDeletionBatch_deleted_card (S j)) (old j) i)
              then (1 : ℂ) else 0) *
            ∑ b : (j : J) → ↥(P j),
              markedRawEdgeFreePrimeMass ν d b *
                (if MarkedRawEdgeRetrievedSlots
                  (fun j i => (markedRawDeletedTupleCast (S j).1
                    (markedRawDeletionBatch_deleted_card (S j)) (old j) i).1) b
                  then (1 : ℂ) else 0) *
                H old b (fun j => markedRawSurvivorTupleCast (S j).1
                  (markedRawDeletionBatch_survivor_card (hk j) (S j)) (old j))) =
      ∑ survivors : (j : J) → Fin (n j) → MarkedRawParticle (P j),
        ((∏ j, ∏ i, ν j (survivors j i).1) /
          (∏ j, (Nat.factorial (n j) : ℂ))) *
          ∑ b : (j : J) → ↥(P j), (∏ j, ν j (b j)) *
            H (fun j i => Fin.addCases (survivors j)
              (markedRawAnchoredBatch (P j) z hz (d j) (fun _ => b j))
              (Fin.cast (hk j).symm i)) b survivors := by
  classical
  rw [markedRawEdge_joint_retrieval_pairing P ν z hz hk
    (fun old retrieved survivors => ∑ b : (j : J) → ↥(P j),
      markedRawEdgeFreePrimeMass ν d b *
        (if MarkedRawEdgeRetrievedSlots retrieved b then (1 : ℂ) else 0) *
        H old b survivors)
    (by
      intro retrieved survivors old σ
      apply Finset.sum_congr rfl
      intro b _
      congr 1
      exact hH b survivors old σ)]
  apply Finset.sum_congr rfl
  intro survivors _
  congr 1
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  simp only [markedRawEdgeRetrievedSlots_iff]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq']
  rw [← mul_assoc, markedRawEdge_retrieved_slots_mass ν d hd b]
  simp only [Finset.mem_univ, ite_true]

end
end ArtinMatthews
