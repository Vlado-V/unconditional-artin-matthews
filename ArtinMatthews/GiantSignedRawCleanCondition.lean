module

public import ArtinMatthews.GiantSignedRawCleanSplit
public import ArtinMatthews.GiantSignedAuxiliaryBan


set_option backward.privateInPublic true
@[expose] public section

/-! On the actual clean choice, the full auxiliary exclusion reduces to
the big-label exclusion by the original cross-band disjointness. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [Fintype (GiantTwoSidedResidueState PS (k+ell))]
    {C : B → Finset (Fin k)}

omit [Fintype B] [DecidableEq S] [DecidableEq B]
  [Fintype (GiantTwoSidedResidueState PS (k+ell))] in
theorem giantSignedRawClean_auxiliary_small
    (hcross : ∀ g j, Disjoint (PB g) (PS j))
    (s : GiantSignedState PS PB (k+ell))
    (r : GiantSignedRawEdgeMove PS PB ell C s.2.2)
    (g : B) (a : C g) (j : S) (i : Fin (k+ell)) :
    (r.auxiliary g a).val ≠ ((giantSignedRawEdgeSmallSource s r).val.2 j i).val ∧
      (r.auxiliary g a).val ≠ (r.smallTarget.val.2 j i).val := by
  have hd := Finset.disjoint_left.mp (hcross g j)
  constructor
  · intro he
    exact hd (r.auxiliary g a).property (he.symm ▸ ((giantSignedRawEdgeSmallSource s r).val.2 j i).property)
  · intro he
    exact hd (r.auxiliary g a).property (he.symm ▸ (r.smallTarget.val.2 j i).property)

omit [DecidableEq S] [DecidableEq B]
  [Fintype (GiantTwoSidedResidueState PS (k+ell))] in
theorem giantSignedRawClean_condition_iff
    (hcross : ∀ g j, Disjoint (PB g) (PS j)) (κ : ℤ)
    (s : GiantSignedState PS PB (k+ell))
    (r : GiantSignedRawEdgeMove PS PB ell C s.2.2) (hr : GiantSignedRawEdgeClean r) :
    GiantSignedRawEdgeCondition κ s r ↔
      (∀ g : S, ∀ i : Fin k, r.smallTarget.val.2 g (Fin.castAdd ell i) =
        (giantSignedRawEdgeSmallSource s r).val.2 g (Fin.castAdd ell i)) ∧
      r.smallTarget.val.1 =
        giantTwoSidedResidueTranslate (κ * (giantSignedRawEdgeProduct s r : ℤ))
          (giantSignedRawEdgeSmallSource s r).val.1 ∧
      IdealCopied C (giantSignedRawEdgeBigSource s r) r.bigTarget ∧
      GiantSignedAuxiliaryBan C (giantSignedRawEdgeBigSource s r) r.bigTarget r.auxiliary := by
  constructor
  · rintro ⟨hsmall, hshift, hcopy, _, haux⟩
    refine ⟨hsmall, hshift, hcopy, ?_⟩
    intro g j a i
    exact (haux g a).2 j i
  · rintro ⟨hsmall, hshift, hcopy, haux⟩
    refine ⟨hsmall, hshift, hcopy, ?_, ?_⟩
    · intro g i
      have hzero : (r.choice.1 g).card = 0 := by
        rw [congrFun hr.1 g]
        rfl
      have hi : i.val < 0 := lt_of_lt_of_eq i.isLt hzero
      exact (Nat.not_lt_zero _ hi).elim
    · intro g a
      exact ⟨fun j i => giantSignedRawClean_auxiliary_small hcross s r g a j i,
        fun j i => haux g j a i⟩

end
end ArtinMatthews
