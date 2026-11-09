module

public import ArtinMatthews.GiantSignedChronologicalLifetime


set_option backward.privateInPublic true
@[expose] public section

/-! Actual old pending indices either survive or are promoted across
an edge. At a visit an old index survives exactly when it is not deleted. -/

namespace ArtinMatthews
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}
    (h : GiantSignedChronologicalChoices PS PB ell C batch)

def GiantSignedChronologicalActive (i : Fin (n+1)) (g : B) (p : PB g) : Prop :=
  ∃ j, (h.state i).2.1 g j = p

def GiantSignedChronologicalPendingBefore (i : Fin (n+1)) (g : B) (p : PB g) : Prop :=
  ∃ j : Fin ((h.state i).2.2.1 g), ((h.state i).2.2.2 g j).1 = p

def GiantSignedChronologicalPendingAfter (i : Fin (n+1)) (g : B) (p : PB g) : Prop :=
  ∃ j : Fin ((giantSignedChronologicalGhostTarget h i).1 g),
    ((giantSignedChronologicalGhostTarget h i).2 g j).1 = p

theorem giantSignedChronologicalLiveAt_before_iff (i : Fin (n+1)) (g : B) (p : PB g) :
    GiantSignedChronologicalLiveAt h g p (2*i.val) ↔
      GiantSignedChronologicalActive h i g p ∨ GiantSignedChronologicalPendingBefore h i g p := by
  rw [giantSignedChronologicalLiveAt_before]
  constructor
  · rintro ⟨j | j,hj⟩
    · exact Or.inl ⟨j,hj⟩
    · exact Or.inr ⟨j,hj⟩
  · rintro (⟨j,hj⟩ | ⟨j,hj⟩)
    · exact ⟨.inl j,hj⟩
    · exact ⟨.inr j,hj⟩

theorem giantSignedChronologicalLiveAt_after_iff (i : Fin (n+1)) (g : B) (p : PB g) :
    GiantSignedChronologicalLiveAt h g p (2*i.val+1) ↔
      GiantSignedChronologicalActive h i g p ∨ GiantSignedChronologicalPendingAfter h i g p := by
  rw [giantSignedChronologicalLiveAt_after]
  constructor
  · rintro ⟨j | j,hj⟩
    · exact Or.inl ⟨j,hj⟩
    · exact Or.inr ⟨j,hj⟩
  · rintro (⟨j,hj⟩ | ⟨j,hj⟩)
    · exact ⟨.inl j,hj⟩
    · exact ⟨.inr j,hj⟩

theorem giantSignedChronologicalOldGhost_survives (i : Fin (n+1)) (g : B)
    (j : Fin ((h.state i).2.2.1 g)) (hj : j ∉ h.deleted i g) :
    GiantSignedChronologicalPendingAfter h i g ((h.state i).2.2.2 g j).1 := by
  let e := (h.deleted i g)ᶜ.orderEmbOfFin rfl
  have hr : j ∈ Set.range e := by
    change j ∈ Set.range ((h.deleted i g)ᶜ.orderEmbOfFin rfl)
    rw [Finset.range_orderEmbOfFin]
    exact Finset.mem_compl.mpr hj
  obtain ⟨z,hz⟩ := hr
  have hp := giantSignedGhostTarget_survivor (giantSignedMemoryGroupEquiv PB (h.state i).2.2 g)
    (h.deleted i g) (h.born i g) z
  refine ⟨Fin.castAdd (batch i g) z,?_⟩
  exact (congrArg Sigma.fst hp).trans (congrArg (fun a => ((h.state i).2.2.2 g a).1) hz)

variable (κ : Fin n → ℤ) (ha : GiantSignedChronologicalAdmissible κ h)
    (hd : GiantSignedBirthDistinct (giantSignedChronologicalBirthData h))

include ha hd in
theorem giantSignedChronologicalPendingBefore_not_active (i : Fin (n+1)) (g : B) (p : PB g)
    (hp : GiantSignedChronologicalPendingBefore h i g p) : ¬ GiantSignedChronologicalActive h i g p := by
  rintro ⟨j,hj⟩
  obtain ⟨z,hz⟩ := hp
  have hinj := giantSignedBirthLineage_injective (giantSignedChronologicalPreLineage h κ ha i g) hd
  have hnot : (Sum.inl j : GiantSignedStateLiveSlots (h.state i) g) = Sum.inr z := hinj (hj.trans hz.symm)
  cases hnot

include ha hd in
theorem giantSignedChronologicalPendingAfter_not_active (i : Fin (n+1)) (g : B) (p : PB g)
    (hp : GiantSignedChronologicalPendingAfter h i g p) : ¬ GiantSignedChronologicalActive h i g p := by
  rintro ⟨j,hj⟩
  obtain ⟨z,hz⟩ := hp
  let l := giantSignedChronologicalVisitLineage h i g (giantSignedChronologicalPreLineage h κ ha i g)
  have hinj := giantSignedBirthLineage_injective l hd
  have hnot : (Sum.inl j : GiantSignedStateLiveSlots (giantSignedChronologicalAfterVisitState h i) g) =
      Sum.inr z := hinj (hj.trans hz.symm)
  cases hnot

include ha in
theorem giantSignedChronologicalPendingAfter_lives_next (i : Fin n) (g : B) (p : PB g)
    (hp : GiantSignedChronologicalPendingAfter h i.castSucc g p) :
    GiantSignedChronologicalLiveAt h g p (2*i.succ.val) := by
  classical
  obtain ⟨j,hj⟩ := hp
  let c := h.edge i
  let R := giantSignedEdgeRetrievedIndices c g
  let m := giantSignedChronologicalGhostTarget h i.castSucc
  apply (giantSignedChronologicalLiveAt_before_iff h i.succ g p).mpr
  by_cases hr : j ∈ R
  · change j ∈ Finset.univ.map (c.2.2 g) at hr
    obtain ⟨z,_,hz⟩ := Finset.mem_map.mp hr
    let slot := giantTwoSidedPatternFreeSlot (C i g) ell
      (giantSignedPatternFreeSlotEquiv (C i g) ell ((c.2.1 g).orderEmbOfFin rfl z))
    refine Or.inl ⟨h.targetBigPermutation i g slot,?_⟩
    exact (congrArg Sigma.fst ((ha.promotion i).1 g z)).symm.trans
      ((congrArg (fun a => (m.2 g a).1) hz).trans hj)
  · let e := Rᶜ.orderEmbOfFin rfl
    have hrange : j ∈ Set.range e := by
      change j ∈ Set.range (Rᶜ.orderEmbOfFin rfl)
      rw [Finset.range_orderEmbOfFin]
      exact Finset.mem_compl.mpr hr
    obtain ⟨z,hz⟩ := hrange
    apply Or.inr
    unfold GiantSignedChronologicalPendingBefore
    rw [(ha.compatible i).2.2.2.1]
    have he := giantSignedEdgeTarget_survivor (κ i * (giantSignedChronologicalProduct h i : ℤ)) m
      (giantSignedPatternFreeLabels (C i) (giantSignedChronologicalBigSource h i)) c g z
    exact ⟨Fin.castAdd (c.1 g).card z,(congrArg Sigma.fst he).trans
      ((congrArg (fun a => (m.2 g a).1) hz).trans hj)⟩

include ha in
theorem giantSignedChronologicalPendingAfter_last (g : B) (p : PB g) :
    ¬ GiantSignedChronologicalPendingAfter h (Fin.last n) g p := by
  intro hp
  unfold GiantSignedChronologicalPendingAfter at hp
  rw [ha.boundary.2] at hp
  obtain ⟨j,_⟩ := hp
  exact Fin.elim0 j

end
end ArtinMatthews
