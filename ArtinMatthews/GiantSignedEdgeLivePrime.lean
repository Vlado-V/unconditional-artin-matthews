module

public import ArtinMatthews.GiantSignedEdgeLiveIndices
public import ArtinMatthews.GiantSignedEdgeMemory
public import ArtinMatthews.GiantSignedGhostMemoryCoordinates
public import ArtinMatthews.IdealLabelOperator


set_option backward.privateInPublic true
@[expose] public section

/-! The actual copy and hit conditions preserve the prime at each old
origin. A fresh free slot reads its own performed birth. -/
namespace ArtinMatthews
noncomputable section

variable {B : Type*} {PB : B → Finset ℕ} {k ell : ℕ}
    (C : B → Finset (Fin k)) (m : GiantSignedMemory PB)
    (a b : MarkedPhysicalMarking PB (k+ell))
    (c : GiantSignedEdgeChoice (fun g => ell+(C g).card) m.1) (d : ℤ)

theorem giantSignedEdgeLiveOrigin_prime (hcopy : IdealCopied C a b)
    (hhit : GiantSignedEdgeHits d m (giantSignedPatternFreeLabels C b) c) (g : B)
    (s : GiantSignedLiveSlots (k+ell)
      ((giantSignedEdgeTarget d m (giantSignedPatternFreeLabels C a) c).1 g)) :
    giantSignedLivePrime (b g) (giantSignedMemoryGroupEquiv PB
        (giantSignedEdgeTarget d m (giantSignedPatternFreeLabels C a) c) g) s =
      Sum.elim (giantSignedLivePrime (a g) (giantSignedMemoryGroupEquiv PB m g))
        (fun i : {i : Fin (ell+(C g).card) // i ∉ c.2.1 g} =>
          giantSignedPatternFreeLabels C b g i.val)
        (giantSignedEdgeLiveOrigin (C g) (c.1 g) (c.2.1 g) (c.2.2 g) s) := by
  let origin := giantSignedEdgeLiveOrigin (C g) (c.1 g) (c.2.1 g) (c.2.2 g)
  let old := giantSignedMemoryGroupEquiv PB m g
  let new := giantSignedMemoryGroupEquiv PB
    (giantSignedEdgeTarget d m (giantSignedPatternFreeLabels C a) c) g
  let L : GiantSignedLiveSlots (k+ell) (((Finset.univ.map (c.2.2 g))ᶜ).card+(c.1 g).card) → PB g :=
    giantSignedLivePrime (b g) new
  let R : (GiantSignedLiveSlots (k+ell) (m.1 g) ⊕
      {i : Fin (ell+(C g).card) // i ∉ c.2.1 g}) → PB g :=
    Sum.elim (giantSignedLivePrime (a g) old) (fun i => giantSignedPatternFreeLabels C b g i.val)
  change GiantSignedLiveSlots (k+ell) (((Finset.univ.map (c.2.2 g))ᶜ).card+(c.1 g).card) at s
  change L s = R (origin s)
  rcases s with i | i
  · obtain ⟨s, rfl⟩ := (giantSignedCanonicalSlotEquiv (C g) ell).symm.surjective i
    rcases s with j | j
    · change L (.inl (Fin.castAdd ell j.val)) = R (origin (.inl (Fin.castAdd ell j.val)))
      refine (hcopy g j.val j.property).trans ?_
      exact (congrArg R (giantSignedEdgeLiveOrigin_copied (C g) (c.1 g) (c.2.1 g)
        (c.2.2 g) j)).symm
    · rw [giantSignedCanonicalSlotEquiv_symm_free]
      obtain ⟨s, rfl⟩ := (markedRawSubsetIndexEquiv (c.2.1 g)).surjective j
      rcases s with i | i
      · change L (.inl (giantSignedFreeSlotEmbedding (C g) ell ((c.2.1 g).orderEmbOfFin rfl i))) =
          R (origin (.inl (giantSignedFreeSlotEmbedding (C g) ell ((c.2.1 g).orderEmbOfFin rfl i))))
        refine (congrArg Sigma.fst (hhit g i)).symm.trans ?_
        exact (congrArg R (giantSignedEdgeLiveOrigin_promoted (C g) (c.1 g) (c.2.1 g)
          (c.2.2 g) i)).symm
      · let j : {j : Fin (ell+(C g).card) // j ∉ c.2.1 g} :=
          ⟨((c.2.1 g)ᶜ).orderEmbOfFin rfl i,
            Finset.mem_compl.mp (((c.2.1 g)ᶜ.orderIsoOfFin rfl) i).property⟩
        change R (.inr j) = R (origin (.inl (giantSignedFreeSlotEmbedding (C g) ell j.val)))
        exact (congrArg R (giantSignedEdgeLiveOrigin_fresh (C g) (c.1 g) (c.2.1 g)
          (c.2.2 g) j)).symm
  · refine Fin.addCases ?_ ?_ i
    · intro j
      refine (congrArg Sigma.fst
        (giantSignedEdgeTarget_survivor d m (giantSignedPatternFreeLabels C a) c g j)).trans ?_
      exact (congrArg R (giantSignedEdgeLiveOrigin_survivor (C g) (c.1 g) (c.2.1 g)
        (c.2.2 g) j)).symm
    · intro j
      refine (congrArg Sigma.fst
        (giantSignedEdgeTarget_store d m (giantSignedPatternFreeLabels C a) c g j)).trans ?_
      exact (congrArg R (giantSignedEdgeLiveOrigin_stored (C g) (c.1 g) (c.2.1 g)
        (c.2.2 g) j)).symm

end
end ArtinMatthews
