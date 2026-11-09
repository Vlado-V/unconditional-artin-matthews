module

public import ArtinMatthews.GiantSignedUniformBirthFrame


set_option backward.privateInPublic true
@[expose] public section

/-! The full canonical marking splits into copied slots and the actual
free-slot carrier of the edge row. Both injections are the source slot maps. -/
namespace ArtinMatthews
noncomputable section

def giantSignedCanonicalSlotEquiv {k : ℕ} (C : Finset (Fin k)) (ell : ℕ) :
    Fin (k+ell) ≃ {i : Fin k // i ∉ C} ⊕ Fin (ell+C.card) :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumCongr
      ((Equiv.sumCompl (fun i : Fin k => i ∈ C)).symm.trans (Equiv.sumComm _ _))
      (Equiv.refl (Fin ell))).trans
      ((Equiv.sumAssoc _ _ _).trans
        (Equiv.sumCongr (Equiv.refl _) (giantSignedPatternFreeSlotEquiv C ell).symm)))

theorem giantSignedCanonicalSlotEquiv_symm_copied {k : ℕ} (C : Finset (Fin k)) (ell : ℕ)
    (i : {i : Fin k // i ∉ C}) :
    (giantSignedCanonicalSlotEquiv C ell).symm (.inl i) = Fin.castAdd ell i.val := rfl

theorem giantSignedCanonicalSlotEquiv_symm_free {k : ℕ} (C : Finset (Fin k)) (ell : ℕ)
    (i : Fin (ell+C.card)) :
    (giantSignedCanonicalSlotEquiv C ell).symm (.inr i) = giantSignedFreeSlotEmbedding C ell i := by
  change _ = giantTwoSidedPatternFreeSlot C ell (giantSignedPatternFreeSlotEquiv C ell i)
  unfold giantSignedCanonicalSlotEquiv
  simp only [Equiv.symm_trans_apply, Equiv.sumCongr_symm, Equiv.symm_symm,
    Equiv.sumCongr_apply, Sum.map_inr]
  generalize giantSignedPatternFreeSlotEquiv C ell i = s
  cases s <;> rfl

theorem giantSignedCanonicalSlotEquiv_copied {k : ℕ} (C : Finset (Fin k)) (ell : ℕ)
    (i : {i : Fin k // i ∉ C}) :
    giantSignedCanonicalSlotEquiv C ell (Fin.castAdd ell i.val) = .inl i := by
  rw [← giantSignedCanonicalSlotEquiv_symm_copied C ell i, Equiv.apply_symm_apply]

theorem giantSignedCanonicalSlotEquiv_free {k : ℕ} (C : Finset (Fin k)) (ell : ℕ)
    (i : Fin (ell+C.card)) :
    giantSignedCanonicalSlotEquiv C ell (giantSignedFreeSlotEmbedding C ell i) = .inr i := by
  rw [← giantSignedCanonicalSlotEquiv_symm_free C ell i, Equiv.apply_symm_apply]

end
end ArtinMatthews
