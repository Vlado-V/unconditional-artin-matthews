module

public import ArtinMatthews.MarkedMinorArcRawGhostState


set_option backward.privateInPublic true
@[expose] public section

/-! Identity choices in the literal indexed memory update. This supplies the
actual no-store/no-promote edge branch, rather than identifying its memory
coordinates by an assumption. -/
namespace ArtinMatthews
open scoped BigOperators

/-- The increasing survivor enumeration is the original index order when
no old index was removed. -/
theorem markedRawGhostSurvivors_empty_enumeration {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (del : MarkedRawGhostDeletion m) (hdel : ∀ j, del j=∅) (j : J)
    (i : Fin (markedRawGhostSurvivors m del j).card) :
    ((markedRawGhostSurvivors m del j).orderEmbOfFin rfl i : ℕ)=i.1 := by
  classical
  have hc : (markedRawGhostSurvivors m del j).card=(m.1.1 j : ℕ) := by
    simp only [markedRawGhostSurvivors,hdel,Finset.sdiff_empty,Finset.card_univ,Fintype.card_fin]
  have he := Finset.orderEmbOfFin_unique rfl (f := Fin.cast hc)
    (fun k => by simp only [markedRawGhostSurvivors,hdel,Finset.sdiff_empty,Finset.mem_univ])
    (Fin.cast_strictMono hc)
  have hi := congrFun he.symm i
  exact congrArg Fin.val hi

/-- Deleting no old particle and appending no new particle is exactly the
original indexed memory, including its actual size proof and index order. -/
theorem markedRawGhostTargetMemory_empty_eq {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (del : MarkedRawGhostDeletion m)
    (hdel : ∀ j, del j=∅) (l : MarkedRawGhostBirthSizes m del)
    (hl : ∀ j, (l.1 j : ℕ)=0) (births : MarkedRawGhostBirthLabels l) :
    markedRawGhostTargetMemory m z hz del l births=m := by
  classical
  have hk : markedRawGhostTargetSizes m del l=m.1 := by
    apply Subtype.ext
    funext j
    apply Fin.ext
    simp only [markedRawGhostTargetSizes,markedRawGhostSurvivors,hdel,hl,
      Finset.sdiff_empty,Finset.card_univ,Fintype.card_fin,Nat.add_zero]
  apply Sigma.ext hk
  apply Function.hfunext rfl
  simp only [heq_iff_eq]
  rintro j _ rfl
  have hj : ((markedRawGhostTargetSizes m del l).1 j : ℕ)=(m.1.1 j : ℕ) := congrArg (fun k => (k.1 j : ℕ)) hk
  apply (Fin.heq_fun_iff hj).mpr
  intro i
  change Fin.addCases
    (fun k => m.2 j ((markedRawGhostSurvivors m del j).orderEmbOfFin rfl k))
    (fun k => markedRawAnchoredParticle (P j) (births j k) z hz) i=m.2 j _
  have hi : (i : ℕ)<(markedRawGhostSurvivors m del j).card := by
    have hbound := i.2
    change (i : ℕ)<(markedRawGhostSurvivors m del j).card+(l.1 j : ℕ) at hbound
    simpa only [hl,Nat.add_zero] using hbound
  simp only [Fin.addCases]
  split_ifs with hh
  · apply congrArg (m.2 j)
    apply Fin.ext
    exact markedRawGhostSurvivors_empty_enumeration m del hdel j _
  · exact False.elim (hh hi)

end ArtinMatthews
