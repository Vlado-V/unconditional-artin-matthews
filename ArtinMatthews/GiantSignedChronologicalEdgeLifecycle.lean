module

public import ArtinMatthews.GiantSignedChronologicalLiveTransitions


set_option backward.privateInPublic true
@[expose] public section

/-! The actual source stores and target promotions are determined by
the pending populations on the two sides of the edge. -/

namespace ArtinMatthews
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}
    (h : GiantSignedChronologicalChoices PS PB ell C batch)
    (κ : Fin n → ℤ) (ha : GiantSignedChronologicalAdmissible κ h)
    (hd : GiantSignedBirthDistinct (giantSignedChronologicalBirthData h))

include ha in
private theorem chronologicalOldEdge_survives (i : Fin n) (g : B)
    (z : Fin ((giantSignedChronologicalGhostTarget h i.castSucc).1 g))
    (hz : z ∉ giantSignedEdgeRetrievedIndices (h.edge i) g) :
    GiantSignedChronologicalPendingBefore h i.succ g
      ((giantSignedChronologicalGhostTarget h i.castSucc).2 g z).1 := by
  let m := giantSignedChronologicalGhostTarget h i.castSucc
  let R := giantSignedEdgeRetrievedIndices (h.edge i) g
  let e := Rᶜ.orderEmbOfFin rfl
  have hr : z ∈ Set.range e := by
    change z ∈ Set.range (Rᶜ.orderEmbOfFin rfl)
    rw [Finset.range_orderEmbOfFin]
    exact Finset.mem_compl.mpr hz
  obtain ⟨j,hj⟩ := hr
  unfold GiantSignedChronologicalPendingBefore
  rw [(ha.compatible i).2.2.2.1]
  have hp := giantSignedEdgeTarget_survivor (κ i * (giantSignedChronologicalProduct h i : ℤ)) m
    (giantSignedPatternFreeLabels (C i) (giantSignedChronologicalBigSource h i)) (h.edge i) g j
  exact ⟨Fin.castAdd ((h.edge i).1 g).card j,
    (congrArg Sigma.fst hp).trans (congrArg (fun j => (m.2 g j).1) hj)⟩

include ha hd in
theorem giantSignedChronologicalPromote_iff_pending (i : Fin n) (g : B)
    (hinj : Function.Injective (giantSignedPatternFreeLabels (C i) (giantSignedChronologicalBigTarget h i) g))
    (j : Fin (ell+(C i g).card)) :
    j ∈ (h.edge i).2.1 g ↔ GiantSignedChronologicalPendingAfter h i.castSucc g
      (giantSignedPatternFreeLabels (C i) (giantSignedChronologicalBigTarget h i) g j) := by
  let T := (h.edge i).2.1 g
  let target := giantSignedPatternFreeLabels (C i) (giantSignedChronologicalBigTarget h i) g
  let m := giantSignedChronologicalGhostTarget h i.castSucc
  let p := target j
  let R := giantSignedEdgeRetrievedIndices (h.edge i) g
  constructor
  · intro hj
    have hr : j ∈ Set.range (T.orderEmbOfFin rfl) := by rw [Finset.range_orderEmbOfFin]; exact hj
    obtain ⟨z,hz⟩ := hr
    have hp := congrArg Sigma.fst ((ha.promotion i).1 g z)
    exact ⟨(h.edge i).2.2 g z,hp.trans (congrArg target hz)⟩
  · rintro ⟨z,hz⟩
    change (m.2 g z).1 = p at hz
    have hR : z ∈ R := by
      by_contra hNo
      have hp : GiantSignedChronologicalPendingBefore h i.succ g p :=
        hz ▸ chronologicalOldEdge_survives h κ ha i g z hNo
      have hActive : GiantSignedChronologicalActive h i.succ g p := by
        let slot := giantTwoSidedPatternFreeSlot (C i g) ell (giantSignedPatternFreeSlotEquiv (C i g) ell j)
        exact ⟨h.targetBigPermutation i g slot,rfl⟩
      exact giantSignedChronologicalPendingBefore_not_active h κ ha hd i.succ g p hp hActive
    change z ∈ Finset.univ.map ((h.edge i).2.2 g) at hR
    obtain ⟨u,_,hu⟩ := Finset.mem_map.mp hR
    have hp : target (T.orderEmbOfFin rfl u) = target j :=
      (congrArg Sigma.fst ((ha.promotion i).1 g u)).symm.trans
        ((congrArg (fun z => (m.2 g z).1) hu).trans hz)
    exact hinj hp ▸ Finset.orderEmbOfFin_mem T rfl u

include ha hd in
theorem giantSignedChronologicalStore_iff_pending (i : Fin n) (g : B)
    (hinj : Function.Injective (giantSignedPatternFreeLabels (C i) (giantSignedChronologicalBigSource h i) g))
    (j : Fin (ell+(C i g).card)) :
    j ∈ (h.edge i).1 g ↔ GiantSignedChronologicalPendingBefore h i.succ g
      (giantSignedPatternFreeLabels (C i) (giantSignedChronologicalBigSource h i) g j) := by
  let S' := (h.edge i).1 g
  let source := giantSignedPatternFreeLabels (C i) (giantSignedChronologicalBigSource h i)
  let m := giantSignedChronologicalGhostTarget h i.castSucc
  let p := source g j
  let R := giantSignedEdgeRetrievedIndices (h.edge i) g
  let shift := κ i * (giantSignedChronologicalProduct h i : ℤ)
  have hmem := (ha.compatible i).2.2.2.1
  constructor
  · intro hj
    have hr : j ∈ Set.range (S'.orderEmbOfFin rfl) := by rw [Finset.range_orderEmbOfFin]; exact hj
    obtain ⟨z,hz⟩ := hr
    unfold GiantSignedChronologicalPendingBefore
    rw [hmem]
    exact ⟨Fin.natAdd (Rᶜ).card z,
      (congrArg Sigma.fst (giantSignedEdgeTarget_store shift m source (h.edge i) g z)).trans
        (congrArg (source g) hz)⟩
  · intro hp
    unfold GiantSignedChronologicalPendingBefore at hp
    rw [hmem] at hp
    obtain ⟨u,hu⟩ := hp
    change Fin ((Rᶜ).card + S'.card) at u
    revert hu
    refine Fin.addCases ?_ ?_ u
    · intro z hz
      have hp' : GiantSignedChronologicalPendingAfter h i.castSucc g p :=
        ⟨(Rᶜ).orderEmbOfFin rfl z,
          (congrArg Sigma.fst (giantSignedEdgeTarget_survivor shift m source (h.edge i) g z)).symm.trans hz⟩
      have hActive : GiantSignedChronologicalActive h i.castSucc g p := by
        let slot := giantTwoSidedPatternFreeSlot (C i g) ell (giantSignedPatternFreeSlotEquiv (C i g) ell j)
        exact ⟨h.sourceBigPermutation i g slot,rfl⟩
      exact (giantSignedChronologicalPendingAfter_not_active h κ ha hd i.castSucc g p hp' hActive).elim
    · intro z hz
      have he : S'.orderEmbOfFin rfl z = j := hinj
        ((congrArg Sigma.fst (giantSignedEdgeTarget_store shift m source (h.edge i) g z)).symm.trans hz)
      exact he ▸ Finset.orderEmbOfFin_mem S' rfl z

end
end ArtinMatthews
