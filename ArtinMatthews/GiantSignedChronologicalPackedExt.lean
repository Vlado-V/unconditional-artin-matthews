module

public import ArtinMatthews.GiantSignedChronologicalChoices


set_option backward.privateInPublic true
@[expose] public section

/-! Equality of chronological data retains every ordered local move,
with heterogeneous equality only for the dependent old-index types. -/

namespace ArtinMatthews
noncomputable section

variable {S B : Type*} [Fintype S]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {batch batch' : Fin (n+1) → B → ℕ}

theorem giantSignedChronologicalChoices_heq
    (h : GiantSignedChronologicalChoices PS PB ell C batch)
    (h' : GiantSignedChronologicalChoices PS PB ell C batch')
    (hbatch : batch = batch') (hs : h.state = h'.state)
    (hπS : h.sourceSmallPermutation = h'.sourceSmallPermutation)
    (hτS : h.targetSmallPermutation = h'.targetSmallPermutation)
    (hπB : h.sourceBigPermutation = h'.sourceBigPermutation)
    (hτB : h.targetBigPermutation = h'.targetBigPermutation)
    (haux : h.auxiliary = h'.auxiliary)
    (hghost : ∀ v g, HEq (giantSignedFixedGhostMove (h.state v).2.2 (batch v) (h.deleted v) (h.born v) g)
      (giantSignedFixedGhostMove (h'.state v).2.2 (batch' v) (h'.deleted v) (h'.born v) g))
    (hedge : ∀ i, HEq (h.edge i) (h'.edge i)) : HEq h h' := by
  subst batch'
  rcases h with ⟨state,deleted,born,πS,τS,πB,τB,aux,edge⟩
  rcases h' with ⟨state',deleted',born',πS',τS',πB',τB',aux',edge'⟩
  dsimp only at hs hπS hτS hπB hτB haux hghost hedge
  subst state'
  subst πS'
  subst τS'
  subst πB'
  subst τB'
  subst aux'
  have hd : deleted = deleted' := by
    funext v g
    exact congrArg Sigma.fst (eq_of_heq (hghost v g))
  subst deleted'
  have hb : born = born' := by
    funext v g
    have he := congrArg Sigma.snd (eq_of_heq (hghost v g))
    exact eq_of_heq ((Sigma.mk.inj_iff.mp he).2)
  subst born'
  have he : edge = edge' := funext fun i => eq_of_heq (hedge i)
  subst edge'
  rfl

end
end ArtinMatthews
