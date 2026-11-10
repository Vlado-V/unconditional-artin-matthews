module

public import ArtinMatthews.MarkedMinorArcRawGhostState
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Exact indexed hit counts after the literal signed-ghost transition.
Repeated particle values are counted by their original indices. -/
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Surviving old hits are precisely the old hit-index set minus deletions. -/
theorem markedRawGhost_survivor_hit_count {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (del : MarkedRawGhostDeletion m) (j : J) :
    (∑ k : Fin (markedRawGhostSurvivors m del j).card,
      if MarkedRawParticleHits (P j) z hz
        (m.2 j ((markedRawGhostSurvivors m del j).orderEmbOfFin rfl k)) then (1:ℕ) else 0)=
      (markedRawGroupHitIndices m j z hz \ del j).card := by
  classical
  let S := markedRawGhostSurvivors m del j
  have he := Equiv.sum_comp (S.orderIsoOfFin rfl).toEquiv
    (fun k : S => if MarkedRawParticleHits (P j) z hz (m.2 j k.1) then (1:ℕ) else 0)
  have hs : S.filter (fun k => MarkedRawParticleHits (P j) z hz (m.2 j k))=
      markedRawGroupHitIndices m j z hz \ del j := by
    ext k
    simp only [S,markedRawGhostSurvivors,markedRawGroupHitIndices,
      Finset.mem_filter,Finset.mem_sdiff,Finset.mem_univ,true_and]
    tauto
  calc
    _ = ∑ k : S, if MarkedRawParticleHits (P j) z hz (m.2 j k.1) then (1:ℕ) else 0 := by
      change (∑ k : Fin S.card, if MarkedRawParticleHits (P j) z hz
        (m.2 j (S.orderEmbOfFin rfl k)) then (1:ℕ) else 0)=_ at he
      exact he
    _ = ∑ k ∈ S, if MarkedRawParticleHits (P j) z hz (m.2 j k) then (1:ℕ) else 0 :=
      Finset.sum_coe_sort S (fun k : Fin (m.1.1 j : ℕ) =>
        if MarkedRawParticleHits (P j) z hz (m.2 j k) then (1:ℕ) else 0)
    _ = _ := by rw [Finset.sum_boole,hs]; simp only [Nat.cast_id]

/-- The literal target memory has exactly the old surviving hits and one
hit per indexed birth. Ineligible old deletions are explicitly excluded. -/
theorem markedRawGhostTargetMemory_group_hits {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (del : MarkedRawGhostDeletion m)
    (hdel : MarkedRawGhostDeletionAllowed m z hz del)
    (l : MarkedRawGhostBirthSizes m del) (births : MarkedRawGhostBirthLabels l) (j : J) :
    (markedRawGroupHitIndices (markedRawGhostTargetMemory m z hz del l births) j z hz).card=
      (markedRawGroupHitIndices m j z hz).card-(del j).card+(l.1 j : ℕ) := by
  classical
  have hcard : (markedRawGroupHitIndices (markedRawGhostTargetMemory m z hz del l births) j z hz).card=
      ∑ k, if MarkedRawParticleHits (P j) z hz
        ((markedRawGhostTargetMemory m z hz del l births).2 j k) then (1:ℕ) else 0 := by
    unfold markedRawGroupHitIndices
    simp only [Finset.sum_boole,Nat.cast_id]
  rw [hcard]
  change (∑ k : Fin ((markedRawGhostSurvivors m del j).card+(l.1 j : ℕ)),
    if MarkedRawParticleHits (P j) z hz
      (Fin.addCases
        (fun k => m.2 j ((markedRawGhostSurvivors m del j).orderEmbOfFin rfl k))
        (fun k => markedRawAnchoredParticle (P j) (births j k) z hz) k) then (1:ℕ) else 0)=_
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left,Fin.addCases_right,markedRawAnchoredParticle_hits,ite_true,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  rw [markedRawGhost_survivor_hit_count,Finset.card_sdiff_of_subset (hdel j)]
  simp only [Nat.cast_id]

/-- Exact total pending hit count in the actual target state. -/
theorem markedRawGhostTargetMemory_total_hits {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (del : MarkedRawGhostDeletion m)
    (hdel : MarkedRawGhostDeletionAllowed m z hz del)
    (l : MarkedRawGhostBirthSizes m del) (births : MarkedRawGhostBirthLabels l) :
    markedRawPendingHits (markedRawGhostTargetMemory m z hz del l births) z hz=
      ∑ j, ((markedRawGroupHitIndices m j z hz).card-(del j).card+(l.1 j : ℕ)) := by
  rw [markedRawPendingHits_eq_sum_card]
  exact Finset.sum_congr rfl (fun j _ => markedRawGhostTargetMemory_group_hits m z hz del hdel l births j)

end ArtinMatthews
