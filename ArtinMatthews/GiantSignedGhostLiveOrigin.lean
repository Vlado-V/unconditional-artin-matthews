module

public import ArtinMatthews.GiantSignedGhostRow


set_option backward.privateInPublic true
@[expose] public section

/-! An actual ghost move gives distinct origins for its live output
slots. Active labels and ordered old survivors keep their original
indices, and the appended batch uses its actual birth indices. -/
namespace ArtinMatthews
noncomputable section

abbrev GiantSignedLiveSlots (M degree : ℕ) := Fin M ⊕ Fin degree

def giantSignedLivePrime {P : Finset ℕ} {M : ℕ}
    (active : Fin M → P) (m : GiantSignedGroupMemory P) : GiantSignedLiveSlots M m.1 → P :=
  Sum.elim active (fun i => (m.2 i).1)

def giantSignedGhostLiveSplit (M s b : ℕ) :
    GiantSignedLiveSlots M (s+b) ≃ GiantSignedLiveSlots M s ⊕ Fin b :=
  (Equiv.sumCongr (Equiv.refl (Fin M)) finSumFinEquiv.symm).trans
    (Equiv.sumAssoc (Fin M) (Fin s) (Fin b)).symm

def giantSignedGhostLiveOrigin {P : Finset ℕ} (M : ℕ) (m : GiantSignedGroupMemory P)
    (deleted : Finset (Fin m.1)) {b : ℕ} (born : Fin b → P) :
    GiantSignedLiveSlots M (giantSignedGhostTarget m deleted born).1 ↪
      (GiantSignedLiveSlots M m.1 ⊕ Fin b) := by
  classical
  let e := giantSignedGhostLiveSplit M (deletedᶜ).card b
  let s := (deletedᶜ).orderEmbOfFin rfl
  refine ⟨Sum.map (Sum.map id s) id ∘ e, ?_⟩
  exact (Sum.map_injective.mpr
    ⟨Sum.map_injective.mpr ⟨Function.injective_id, s.injective⟩,
      Function.injective_id⟩).comp e.injective

theorem giantSignedGhostLiveOrigin_active {P : Finset ℕ} {M b : ℕ}
    (m : GiantSignedGroupMemory P) (deleted : Finset (Fin m.1)) (born : Fin b → P) (i : Fin M) :
    giantSignedGhostLiveOrigin M m deleted born (.inl i) = .inl (.inl i) := rfl

theorem giantSignedGhostLiveOrigin_survivor {P : Finset ℕ} {M b : ℕ}
    (m : GiantSignedGroupMemory P) (deleted : Finset (Fin m.1)) (born : Fin b → P)
    (i : Fin (deletedᶜ).card) :
    giantSignedGhostLiveOrigin M m deleted born (.inr (Fin.castAdd b i)) =
      .inl (.inr ((deletedᶜ).orderEmbOfFin rfl i)) := by
  change Sum.map (Sum.map id ((deletedᶜ).orderEmbOfFin rfl)) id
    ((Equiv.sumAssoc (Fin M) (Fin (deletedᶜ).card) (Fin b)).symm
      (.inr (finSumFinEquiv.symm (Fin.castAdd b i)))) = _
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

theorem giantSignedGhostLiveOrigin_born {P : Finset ℕ} {M b : ℕ}
    (m : GiantSignedGroupMemory P) (deleted : Finset (Fin m.1)) (born : Fin b → P) (i : Fin b) :
    giantSignedGhostLiveOrigin M m deleted born (.inr (Fin.natAdd (deletedᶜ).card i)) = .inr i := by
  change Sum.map (Sum.map id ((deletedᶜ).orderEmbOfFin rfl)) id
    ((Equiv.sumAssoc (Fin M) (Fin (deletedᶜ).card) (Fin b)).symm
      (.inr (finSumFinEquiv.symm (Fin.natAdd (deletedᶜ).card i)))) = _
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl

theorem giantSignedGhostLiveOrigin_prime {P : Finset ℕ} {M b : ℕ}
    (active : Fin M → P) (m : GiantSignedGroupMemory P) (deleted : Finset (Fin m.1))
    (born : Fin b → P) (s : GiantSignedLiveSlots M (giantSignedGhostTarget m deleted born).1) :
    giantSignedLivePrime active (giantSignedGhostTarget m deleted born) s =
      Sum.elim (giantSignedLivePrime active m) born (giantSignedGhostLiveOrigin M m deleted born s) := by
  rcases s with i | i
  · rfl
  · change Fin ((deletedᶜ).card + b) at i
    refine Fin.addCases ?_ ?_ i
    · intro j
      rw [giantSignedGhostLiveOrigin_survivor]
      change ((giantSignedGhostTarget m deleted born).2 (Fin.castAdd b j)).1 = _
      exact congrArg Sigma.fst (giantSignedGhostTarget_survivor m deleted born j)
    · intro j
      rw [giantSignedGhostLiveOrigin_born]
      change ((giantSignedGhostTarget m deleted born).2 (Fin.natAdd (deletedᶜ).card j)).1 = _
      exact congrArg Sigma.fst (giantSignedGhostTarget_born m deleted born j)

end
end ArtinMatthews
