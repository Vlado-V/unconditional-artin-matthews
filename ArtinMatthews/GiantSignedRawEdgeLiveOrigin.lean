module

public import ArtinMatthews.GiantSignedEdgeLivePrime
public import ArtinMatthews.GiantSignedRawEdgeData


set_option backward.privateInPublic true
@[expose] public section

/-! Actual target indices first undo the target slot permutation.
Old active origins then pass through the actual source permutation. -/
namespace ArtinMatthews
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ} {C : B → Finset (Fin k)}
    (κ : ℤ) (s : GiantSignedState PS PB (k+ell))
    (r : GiantSignedRawEdgeMove PS PB ell C s.2.2) (g : B)

def giantSignedRawEdgeLiveOrigin :
    GiantSignedLiveSlots (k+ell) ((giantSignedRawEdgeTarget κ s r).2.2.1 g) ↪
      (GiantSignedLiveSlots (k+ell) (s.2.2.1 g) ⊕
        {i : Fin (ell+(C g).card) // i ∉ r.choice.2.1 g}) :=
  ((Equiv.sumCongr (r.targetBigPermutation g).symm (Equiv.refl _)).toEmbedding.trans
    (giantSignedEdgeLiveOrigin (C g) (r.choice.1 g) (r.choice.2.1 g) (r.choice.2.2 g))).trans
      (Equiv.sumCongr
        (Equiv.sumCongr (r.sourceBigPermutation g) (Equiv.refl _)) (Equiv.refl _)).toEmbedding

theorem giantSignedRawEdgeLiveOrigin_prime (hc : GiantSignedRawEdgeCondition κ s r)
    (hh : GiantSignedEdgeHits (κ * (giantSignedRawEdgeProduct s r : ℤ)) s.2.2
      (giantSignedPatternFreeLabels C r.bigTarget) r.choice)
    (z : GiantSignedLiveSlots (k+ell) ((giantSignedRawEdgeTarget κ s r).2.2.1 g)) :
    giantSignedLivePrime ((giantSignedRawEdgeTarget κ s r).2.1 g)
        (giantSignedMemoryGroupEquiv PB (giantSignedRawEdgeTarget κ s r).2.2 g) z =
      Sum.elim (giantSignedLivePrime (s.2.1 g) (giantSignedMemoryGroupEquiv PB s.2.2 g))
        (fun i : {i : Fin (ell+(C g).card) // i ∉ r.choice.2.1 g} =>
          giantSignedPatternFreeLabels C r.bigTarget g i.val)
        (giantSignedRawEdgeLiveOrigin κ s r g z) := by
  let u := Sum.map (r.targetBigPermutation g).symm id z
  let w := giantSignedEdgeLiveOrigin (C g) (r.choice.1 g) (r.choice.2.1 g) (r.choice.2.2 g) u
  have he := giantSignedEdgeLiveOrigin_prime C s.2.2 (giantSignedRawEdgeBigSource s r) r.bigTarget
    r.choice (κ * (giantSignedRawEdgeProduct s r : ℤ)) hc.2.2.1 hh g u
  have hl : giantSignedLivePrime ((giantSignedRawEdgeTarget κ s r).2.1 g)
      (giantSignedMemoryGroupEquiv PB (giantSignedRawEdgeTarget κ s r).2.2 g) z =
      giantSignedLivePrime (r.bigTarget g)
        (giantSignedMemoryGroupEquiv PB (giantSignedRawEdgeTarget κ s r).2.2 g) u := by
    cases z <;> rfl
  refine hl.trans (he.trans ?_)
  change Sum.elim (giantSignedLivePrime ((giantSignedRawEdgeBigSource s r) g)
      (giantSignedMemoryGroupEquiv PB s.2.2 g)) _ w =
    Sum.elim (giantSignedLivePrime (s.2.1 g) (giantSignedMemoryGroupEquiv PB s.2.2 g)) _
      (Sum.map (Sum.map (r.sourceBigPermutation g) id) id w)
  rcases w with (i | i) | i <;> rfl

end
end ArtinMatthews
