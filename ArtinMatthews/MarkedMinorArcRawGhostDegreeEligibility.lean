module

public import ArtinMatthews.MarkedMinorArcRawGhostDegreeFibers


set_option backward.privateInPublic true
@[expose] public section

/-! Exact deleted-hit eligibility in the native fixed-degree tuple
coordinates, and unrestricted finite-sum versions of the degree fibers. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem markedRawSubset_all_iff_deleted {X : Type*} {k d : ℕ}
    (S : Finset (Fin k)) (hd : S.card=d) (a : Fin k → X) (p : X → Prop) :
    (∀ i ∈ S, p (a i)) ↔ ∀ i, p (markedRawDeletedTupleCast S hd a i) := by
  cases hd
  constructor
  · intro h i
    change p (a (S.orderEmbOfFin rfl i))
    exact h _ (S.orderIsoOfFin rfl i).2
  · intro h i hi
    obtain ⟨j,hj⟩ := (S.orderIsoOfFin rfl).surjective ⟨i,hi⟩
    have hv : S.orderEmbOfFin rfl j=i := congrArg Subtype.val hj
    simpa only [markedRawDeletedTupleCast,Fin.cast_refl,id_eq,markedRawSubsetTupleEquiv_deleted,hv] using h j

def MarkedRawGhostDegreeAllowed {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) {B : ℕ} (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (a : MarkedRawGhostDegreeShape J B)
    (old : (j : J) → Fin (a.1.survivors j+a.1.deleted j) → MarkedRawParticle (P j)) : Prop :=
  MarkedRawGhostDeletionAllowed ⟨markedRawGhostDegreesSourceSizes a.1,old⟩ z hz (fun j => (a.2 j).1)

set_option backward.isDefEq.respectTransparency false in
theorem markedRawGhostDegreeAllowed_iff {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) {B : ℕ} (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (a : MarkedRawGhostDegreeShape J B)
    (old : (j : J) → Fin (a.1.survivors j+a.1.deleted j) → MarkedRawParticle (P j)) :
    MarkedRawGhostDegreeAllowed P z hz a old ↔
      ∀ j i, MarkedRawParticleHits (P j) z hz
        (markedRawDeletedTupleCast (a.2 j).1 (markedRawDeletionBatch_deleted_card (a.2 j)) (old j) i) := by
  unfold MarkedRawGhostDegreeAllowed MarkedRawGhostDeletionAllowed
  constructor
  · intro h j
    apply (markedRawSubset_all_iff_deleted (a.2 j).1
      (markedRawDeletionBatch_deleted_card (a.2 j)) (old j) (MarkedRawParticleHits (P j) z hz)).mp
    intro i hi
    exact (Finset.mem_filter.mp (h j hi)).2
  · intro h j i hi
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,(markedRawSubset_all_iff_deleted (a.2 j).1
      (markedRawDeletionBatch_deleted_card (a.2 j)) (old j) (MarkedRawParticleHits (P j) z hz)).mpr (h j) i hi⟩

set_option backward.isDefEq.respectTransparency false in
theorem markedRawGhost_degree_payload_sum {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) {B : ℕ} (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (a : MarkedRawGhostDegreeShape J B) {T : Type*} [AddCommMonoid T]
    (f : MarkedRawGhostDegreePayload P z hz a → T) :
    (∑ data : MarkedRawGhostDegreePayload P z hz a, f data) =
      ∑ old : (j : J) → Fin (a.1.survivors j+a.1.deleted j) → MarkedRawParticle (P j),
        ∑ births : (j : J) → Fin (a.1.born j) → ↥(P j),
          if h : MarkedRawGhostDegreeAllowed P z hz a old then f ⟨(old,births),h⟩ else 0 := by
  classical
  have h := Finset.sum_dite (s := Finset.univ) (fun data h => f ⟨data,h⟩)
    (fun (_ : ((j : J) → Fin (a.1.survivors j+a.1.deleted j) → MarkedRawParticle (P j)) ×
      ((j : J) → Fin (a.1.born j) → ↥(P j))) _ => (0:T))
  have hs : (∑ data : ((j : J) → Fin (a.1.survivors j+a.1.deleted j) → MarkedRawParticle (P j)) ×
      ((j : J) → Fin (a.1.born j) → ↥(P j)),
      if h : MarkedRawGhostDegreeAllowed P z hz a data.1 then f ⟨data,h⟩ else 0)=
      ∑ data : MarkedRawGhostDegreePayload P z hz a, f data := by
    erw [h]
    simp only [Finset.sum_const_zero,add_zero]
    exact (Equiv.subtypeEquivRight (by simp)).sum_comp (fun data : MarkedRawGhostDegreePayload P z hz a => f data)
  exact hs.symm.trans (Fintype.sum_prod_type _)

end
end ArtinMatthews
