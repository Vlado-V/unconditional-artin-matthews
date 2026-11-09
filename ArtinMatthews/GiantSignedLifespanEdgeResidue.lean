module

public import ArtinMatthews.GiantSignedLifespanEdgeSlots


set_option backward.privateInPublic true
@[expose] public section

/-! The actual retrieved particles hit zero after the same dilation.
Stores begin at the current active anchor and use the same translation. -/
namespace ArtinMatthews
noncomputable section

variable {P : Finset ℕ} {n t : ℕ} {A : (p : P) → Finset (Fin n)}
    (c : ∀ p, GiantSignedResidueLifespanChoice (A p)) (offset : Fin n → ℤ)
    (q : Fin n → ℝ)

theorem giantSignedLifespanResidue_active (v : Fin n) (p : P)
    (hweight : giantSignedResidueLifespanWeight p.val offset q (A p) (c p) ≠ 0)
    (hv : v ∈ A p) :
    giantSignedLifespanResidue c offset v p = 0 := by
  unfold giantSignedLifespanResidue
  cases h : giantSignedPrimeLifespanView (A p) (c p) with
  | none => rfl
  | some L =>
      change (offset v : ZMod p.val) - (offset L.start : ZMod p.val) = 0
      exact sub_eq_zero.mpr
        ((giantSignedPrimeLifespanView_offsets_of_weight_ne_zero p.val offset q (A p) (c p) hweight h).2 v hv)

theorem giantSignedLifespanResidue_translate {v w : Fin n} {d : ℤ}
    (hd : offset w = offset v + d) (p : P)
    (hp : giantSignedPrimePendingAfter (c p) v) :
    giantSignedParticleTranslate d ⟨p,giantSignedLifespanResidue c offset v p⟩ =
      (⟨p,giantSignedLifespanResidue c offset w p⟩ : GiantSignedParticle P) := by
  cases h : giantSignedPrimeLifespanView (A p) (c p) with
  | none =>
      simp only [giantSignedPrimePendingAfter, h, Option.elim_none] at hp
  | some L =>
      have he :
          giantSignedLifespanResidue c offset v p + (d : ZMod p.val) =
            giantSignedLifespanResidue c offset w p := by
        simp only [giantSignedLifespanResidue, h, Option.elim_some, hd, Int.cast_add]
        ring
      exact congrArg (Sigma.mk p) he

theorem giantSignedLifespanStore_particle {v w : Fin n} {d : ℤ} (hd : offset w = offset v+d)
    (p : P) (hweight : giantSignedResidueLifespanWeight p.val offset q (A p) (c p) ≠ 0)
    (hv : v ∈ A p) :
    giantSignedParticleAt d p = ⟨p,giantSignedLifespanResidue c offset w p⟩ := by
  obtain ⟨L,h,_⟩ := giantSignedPrimeLifespanView_of_active (A p) (c p) v hv
  have he := (giantSignedPrimeLifespanView_offsets_of_weight_ne_zero
    p.val offset q (A p) (c p) hweight h).2 v hv
  apply congrArg (Sigma.mk p)
  simp only [giantSignedLifespanResidue, h, Option.elim_some, hd, Int.cast_add]
  rw [he]
  ring

theorem giantSignedLifespanRetrieval_hit {v w : Fin n} {d : ℤ}
    (hd : offset w = offset v + d)
    (hweight : ∀ p, giantSignedResidueLifespanWeight p.val offset q (A p) (c p) ≠ 0)
    (target : Fin t → P) (htarget : Function.Injective target) (m : GiantSignedGroupMemory P)
    (hm : GiantSignedLifespanMemory (giantSignedGhostVisitAfter c v) (giantSignedLifespanResidue c offset v) m)
    (i : Fin (giantSignedLifespanPromoteSlots c v w target).card) :
    let T := giantSignedLifespanPromoteSlots c v w target
    giantSignedParticleTranslate d (m.2 (giantSignedLifespanRetrieval c v w target htarget offset m hm i)) =
      giantSignedParticleAt 0 (giantSignedEdgeSelected T target i) := by
  let T := giantSignedLifespanPromoteSlots c v w target
  let p := giantSignedEdgeSelected T target i
  have hp : giantSignedPrimePromote (c p) v w :=
    (giantSignedLifespanPromoteSlots_mem c v w target _).mp (Finset.orderEmbOfFin_mem T rfl i)
  refine (congrArg (giantSignedParticleTranslate d)
    (giantSignedLifespanRetrieval_particle c v w target htarget offset m hm i)).trans ?_
  refine (giantSignedLifespanResidue_translate c offset hd p hp.1).trans ?_
  exact congrArg (Sigma.mk p) ((giantSignedLifespanResidue_active c offset q w p (hweight p) hp.2).trans
    Int.cast_zero.symm)

end
end ArtinMatthews
