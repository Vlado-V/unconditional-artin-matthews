module

public import ArtinMatthews.GiantSignedChronologicalLifespanLocalCoefficient
public import ArtinMatthews.GiantPrimeGhostEndpointInjective


set_option backward.privateInPublic true
@[expose] public section

/-! The original ordered ghost moves determine every lifespan endpoint
and every birth order for the same active-visit sets. -/

namespace ArtinMatthews
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}
    {A : ∀ g, PB g → Finset (Fin (n+1))}
    (h : GiantSignedChronologicalChoices PS PB ell C batch)
    (c : ∀ g p, GiantSignedResidueLifespanChoice (A g p))

theorem giantSignedChronologicalGhostMatch_births (i : Fin (n+1)) (g : B)
    (hm : GiantSignedChronologicalLifespanGhostMatch c h i g) (p : PB g) :
    (∃ j, h.born i g j = p) ↔ giantSignedPrimeGhostBirthAt (c g p) i := by
  obtain ⟨order,he⟩ := hm
  let b := giantSignedGhostVisitBorn (c g) i
  let m := giantSignedMemoryGroupEquiv PB (h.state i).2.2 g
  let F (x : GiantSignedGhostMoves m) : Prop := ∃ j, x.2.2 j = p
  have he' := congrArg F he
  change (∃ j, h.born i g j = p) = (∃ j, giantSignedGhostVisitBornLabels order j = p) at he'
  rw [he',← mem_giantSignedGhostVisitBorn]
  constructor
  · rintro ⟨j,hj⟩
    exact hj ▸ (order j).property
  · intro hp
    obtain ⟨j,hj⟩ := order.surjective ⟨p,hp⟩
    exact ⟨j,congrArg Subtype.val hj⟩

theorem giantSignedChronologicalGhostMatch_deaths (offset : Fin (n+1) → ℤ) (i : Fin (n+1)) (g : B)
    (before : GiantSignedLifespanMemory (giantSignedGhostVisitBefore (c g) i)
      (giantSignedLifespanResidue (c g) offset i) (giantSignedMemoryGroupEquiv PB (h.state i).2.2 g))
    (hm : GiantSignedChronologicalLifespanGhostMatch c h i g) (p : PB g) :
    (∃ j ∈ h.deleted i g, ((h.state i).2.2.2 g j).1 = p) ↔ giantSignedPrimeGhostDeathAt (c g p) i := by
  obtain ⟨order,he⟩ := hm
  let m := giantSignedMemoryGroupEquiv PB (h.state i).2.2 g
  have hd : h.deleted i g = giantSignedGhostVisitDeleted (c g) i m := congrArg Sigma.fst he
  constructor
  · rintro ⟨j,hj,hp⟩
    have he := (mem_giantSignedGhostVisitDeleted (c g) i m (show Fin m.1 from j)).mp (hd ▸ hj)
    exact hp ▸ he
  · intro hp
    have hb := giantSignedPrimeGhostDeathAt_pendingBefore (c g p) i hp
    let p' : ↥(giantSignedGhostVisitBefore (c g) i) :=
      ⟨p,(mem_giantSignedGhostVisitBefore (c g) i p).mpr hb⟩
    let j := before.index p'
    have hj : (m.2 j).1 = p := before.index_prime p'
    have hd' : j ∈ giantSignedGhostVisitDeleted (c g) i m :=
      (mem_giantSignedGhostVisitDeleted (c g) i m j).mpr (hj.symm ▸ hp)
    exact ⟨j,hd.symm ▸ hd',hj⟩

theorem giantSignedChronologicalGhostMatch_choice_unique
    (d : ∀ g p, GiantSignedResidueLifespanChoice (A g p)) (offset : Fin (n+1) → ℤ)
    (beforeC : ∀ i g, GiantSignedLifespanMemory (giantSignedGhostVisitBefore (c g) i)
      (giantSignedLifespanResidue (c g) offset i) (giantSignedMemoryGroupEquiv PB (h.state i).2.2 g))
    (beforeD : ∀ i g, GiantSignedLifespanMemory (giantSignedGhostVisitBefore (d g) i)
      (giantSignedLifespanResidue (d g) offset i) (giantSignedMemoryGroupEquiv PB (h.state i).2.2 g))
    (hc : ∀ i g, GiantSignedChronologicalLifespanGhostMatch c h i g)
    (hd : ∀ i g, GiantSignedChronologicalLifespanGhostMatch d h i g) : c = d := by
  funext g p
  apply giantSignedResidueLifespanChoice_eq_of_ghostEndpoints (c g p) (d g p)
  · intro i
    exact (giantSignedChronologicalGhostMatch_births h c i g (hc i g) p).symm.trans
      (giantSignedChronologicalGhostMatch_births h d i g (hd i g) p)
  · intro i
    exact (giantSignedChronologicalGhostMatch_deaths h c offset i g (beforeC i g) (hc i g) p).symm.trans
      (giantSignedChronologicalGhostMatch_deaths h d offset i g (beforeD i g) (hd i g) p)

theorem giantSignedChronologicalGhostMatch_order_unique (i : Fin (n+1)) (g : B)
    (order order' : Fin (giantSignedGhostVisitBorn (c g) i).card ≃ ↥(giantSignedGhostVisitBorn (c g) i))
    (hm : giantSignedFixedGhostMove (h.state i).2.2 (batch i) (h.deleted i) (h.born i) g =
      giantSignedGhostVisitMove (c g) i (giantSignedMemoryGroupEquiv PB (h.state i).2.2 g) order)
    (hm' : giantSignedFixedGhostMove (h.state i).2.2 (batch i) (h.deleted i) (h.born i) g =
      giantSignedGhostVisitMove (c g) i (giantSignedMemoryGroupEquiv PB (h.state i).2.2 g) order') : order = order' := by
  have h := congrArg Sigma.snd (hm.symm.trans hm')
  have hlabels : giantSignedGhostVisitBornLabels order = giantSignedGhostVisitBornLabels order' :=
    eq_of_heq (Sigma.mk.inj_iff.mp h).2
  apply Equiv.ext
  intro j
  exact Subtype.ext (congrFun hlabels j)

end
end ArtinMatthews
