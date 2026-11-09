module

public import ArtinMatthews.GiantSignedRawEdgeLiveOrigin
public import ArtinMatthews.GiantSignedChronologicalSupport


set_option backward.privateInPublic true
@[expose] public section

/-! Both actual local origins transport to the chronological state array.
The edge memory equality is the original compatible-path condition. -/
namespace ArtinMatthews
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ} {M : ℕ}
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}

abbrev GiantSignedStateLiveSlots (s : GiantSignedState PS PB M) (g : B) :=
  GiantSignedLiveSlots M (s.2.2.1 g)

def giantSignedStateLivePrime (s : GiantSignedState PS PB M) (g : B) :
    GiantSignedStateLiveSlots s g → PB g :=
  giantSignedLivePrime (s.2.1 g) (giantSignedMemoryGroupEquiv PB s.2.2 g)

def giantSignedStateLiveEquiv {s t : GiantSignedState PS PB M} (h : s = t) (g : B) :
    GiantSignedStateLiveSlots s g ≃ GiantSignedStateLiveSlots t g := by
  subst t
  exact Equiv.refl _

theorem giantSignedStateLiveEquiv_prime {s t : GiantSignedState PS PB M} (h : s = t) (g : B)
    (z : GiantSignedStateLiveSlots s g) :
    giantSignedStateLivePrime t g (giantSignedStateLiveEquiv h g z) =
      giantSignedStateLivePrime s g z := by
  subst t
  rfl

def giantSignedChronologicalVisitOrigin (h : GiantSignedChronologicalChoices PS PB ell C batch)
    (i : Fin (n+1)) (g : B) :
    GiantSignedStateLiveSlots (giantSignedChronologicalAfterVisitState h i) g ↪
      (GiantSignedStateLiveSlots (h.state i) g ⊕ Fin (batch i g)) :=
  giantSignedGhostLiveOrigin (k+ell) (giantSignedMemoryGroupEquiv PB (h.state i).2.2 g)
    (h.deleted i g) (h.born i g)

theorem giantSignedChronologicalVisitOrigin_prime
    (h : GiantSignedChronologicalChoices PS PB ell C batch) (i : Fin (n+1)) (g : B)
    (z : GiantSignedStateLiveSlots (giantSignedChronologicalAfterVisitState h i) g) :
    giantSignedStateLivePrime (giantSignedChronologicalAfterVisitState h i) g z =
      Sum.elim (giantSignedStateLivePrime (h.state i) g) (h.born i g)
        (giantSignedChronologicalVisitOrigin h i g z) :=
  giantSignedGhostLiveOrigin_prime _ _ _ _ z

def giantSignedChronologicalEdgeOrigin (κ : Fin n → ℤ)
    (h : GiantSignedChronologicalChoices PS PB ell C batch)
    (hc : GiantSignedChronologicalCompatible κ h) (i : Fin n) (g : B) :
    GiantSignedStateLiveSlots (h.state i.succ) g ↪
      (GiantSignedStateLiveSlots (giantSignedChronologicalAfterVisitState h i.castSucc) g ⊕
        {z : Fin (ell+(C i g).card) // z ∉ (h.edge i).2.1 g}) :=
  (giantSignedStateLiveEquiv (giantSignedChronologicalRawMove_target κ h hc i).symm g).toEmbedding.trans
    (giantSignedRawEdgeLiveOrigin (κ i) (giantSignedChronologicalAfterVisitState h i.castSucc)
      (giantSignedChronologicalRawMove h i) g)

theorem giantSignedChronologicalEdgeOrigin_prime (κ : Fin n → ℤ)
    (h : GiantSignedChronologicalChoices PS PB ell C batch)
    (ha : GiantSignedChronologicalAdmissible κ h) (i : Fin n) (g : B)
    (z : GiantSignedStateLiveSlots (h.state i.succ) g) :
    giantSignedStateLivePrime (h.state i.succ) g z =
      Sum.elim (giantSignedStateLivePrime (giantSignedChronologicalAfterVisitState h i.castSucc) g)
        (fun u : {u : Fin (ell+(C i g).card) // u ∉ (h.edge i).2.1 g} =>
          giantSignedPatternFreeLabels (C i) (giantSignedChronologicalBigTarget h i) g u.val)
        (giantSignedChronologicalEdgeOrigin κ h ha.compatible i g z) := by
  let s := giantSignedChronologicalAfterVisitState h i.castSucc
  let r := giantSignedChronologicalRawMove h i
  let e := giantSignedStateLiveEquiv
    (giantSignedChronologicalRawMove_target κ h ha.compatible i).symm g
  have he := giantSignedStateLiveEquiv_prime
    (giantSignedChronologicalRawMove_target κ h ha.compatible i).symm g z
  rw [← he]
  exact giantSignedRawEdgeLiveOrigin_prime (κ i) s r g
    (giantSignedChronologicalRawMove_condition κ h ha.compatible i) (ha.promotion i).1 (e z)

end
end ArtinMatthews
