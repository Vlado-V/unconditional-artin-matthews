module

public import ArtinMatthews.GiantSignedEdgeLiveParticle
public import ArtinMatthews.GiantSignedRawEdgeLiveOrigin


set_option backward.privateInPublic true
@[expose] public section

/-! The original dilation translates every old live particle. A copied
active label divides the dilation by its literal copied factor. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ} {C : B → Finset (Fin k)}
    (κ : ℤ) (s : GiantSignedState PS PB (k+ell))
    (r : GiantSignedRawEdgeMove PS PB ell C s.2.2)

theorem giantSignedRawEdge_copy_shift_zero (g : B) (i : Fin k) (hi : i ∉ C g) :
    ((κ * (giantSignedRawEdgeProduct s r : ℤ) : ℤ) :
      ZMod (giantSignedRawEdgeBigSource s r g (Fin.castAdd ell i)).val) = 0 := by
  let a := giantSignedRawEdgeBigSource s r
  let p := (a g (Fin.castAdd ell i)).val
  have h1 : p ∣ ∏ l ∈ Finset.univ \ C g, (a g (Fin.castAdd ell l)).val :=
    Finset.dvd_prod_of_mem (fun l => (a g (Fin.castAdd ell l)).val)
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩)
  have h2 : p ∣ giantTwoSidedPatternCopiedProduct C a := h1.trans
    (Finset.dvd_prod_of_mem (fun j => ∏ l ∈ Finset.univ \ C j, (a j (Fin.castAdd ell l)).val)
      (Finset.mem_univ g))
  have hD : p ∣ giantSignedRawEdgeProduct s r :=
    dvd_mul_of_dvd_right (dvd_mul_of_dvd_left h2 _) _
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr
    (dvd_mul_of_dvd_right (Int.ofNat_dvd.mpr hD) κ)

theorem giantSignedRawEdgeLiveOrigin_particle (hc : GiantSignedRawEdgeCondition κ s r)
    (hh : GiantSignedEdgeHits (κ * (giantSignedRawEdgeProduct s r : ℤ)) s.2.2
      (giantSignedPatternFreeLabels C r.bigTarget) r.choice) (g : B)
    (z : GiantSignedLiveSlots (k+ell) ((giantSignedRawEdgeTarget κ s r).2.2.1 g)) :
    giantSignedLiveParticle ((giantSignedRawEdgeTarget κ s r).2.1 g)
        (giantSignedMemoryGroupEquiv PB (giantSignedRawEdgeTarget κ s r).2.2 g) z =
      Sum.elim (fun i => giantSignedParticleTranslate (κ * (giantSignedRawEdgeProduct s r : ℤ))
          (giantSignedLiveParticle (s.2.1 g) (giantSignedMemoryGroupEquiv PB s.2.2 g) i))
        (fun i : {i : Fin (ell+(C g).card) // i ∉ r.choice.2.1 g} =>
          giantSignedParticleAt 0 (giantSignedPatternFreeLabels C r.bigTarget g i.val))
        (giantSignedRawEdgeLiveOrigin κ s r g z) := by
  let d := κ * (giantSignedRawEdgeProduct s r : ℤ)
  let u := Sum.map (r.targetBigPermutation g).symm id z
  let w := giantSignedEdgeLiveOrigin (C g) (r.choice.1 g) (r.choice.2.1 g) (r.choice.2.2 g) u
  have he := giantSignedEdgeLiveOrigin_particle C s.2.2 (giantSignedRawEdgeBigSource s r) r.bigTarget
    r.choice d hc.2.2.1 (giantSignedRawEdge_copy_shift_zero κ s r) hh g u
  have hl : giantSignedLiveParticle ((giantSignedRawEdgeTarget κ s r).2.1 g)
      (giantSignedMemoryGroupEquiv PB (giantSignedRawEdgeTarget κ s r).2.2 g) z =
      giantSignedLiveParticle (r.bigTarget g)
        (giantSignedMemoryGroupEquiv PB (giantSignedRawEdgeTarget κ s r).2.2 g) u := by
    cases z <;> rfl
  refine hl.trans (he.trans ?_)
  change Sum.elim (fun i => giantSignedParticleTranslate d
      (giantSignedLiveParticle ((giantSignedRawEdgeBigSource s r) g)
        (giantSignedMemoryGroupEquiv PB s.2.2 g) i)) _ w =
    Sum.elim (fun i => giantSignedParticleTranslate d
      (giantSignedLiveParticle (s.2.1 g) (giantSignedMemoryGroupEquiv PB s.2.2 g) i)) _
      (Sum.map (Sum.map (r.sourceBigPermutation g) id) id w)
  rcases w with (i | i) | i <;> rfl

end
end ArtinMatthews
