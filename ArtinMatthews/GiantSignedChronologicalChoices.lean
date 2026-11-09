module

public import ArtinMatthews.GiantSignedBirthRank
public import ArtinMatthews.GiantSignedGhostSimultaneous


set_option backward.privateInPublic true
@[expose] public section

/-! Concrete chronological choices of the original signed rows. The
before-visit memories have arbitrary finite degrees. Ghost deletions and
edge promotions use their actual old indices, before any new birth. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {S B : Type*} [Fintype S] {PS : S → Finset ℕ} {PB : B → Finset ℕ}
    {k ell n : ℕ}

def giantSignedFixedGhostMove (m : GiantSignedMemory PB) (b : B → ℕ)
    (deleted : (g : B) → Finset (Fin (m.1 g)))
    (born : (g : B) → Fin (b g) → PB g) : GiantSignedGhostMemoryMoves m :=
  fun g => ⟨deleted g, b g, born g⟩

def giantSignedFixedGhostTarget (m : GiantSignedMemory PB) (b : B → ℕ)
    (deleted : (g : B) → Finset (Fin (m.1 g)))
    (born : (g : B) → Fin (b g) → PB g) : GiantSignedMemory PB :=
  giantSignedGhostMemoryMoveTarget m (giantSignedFixedGhostMove m b deleted born)

theorem giantSignedFixedGhostTarget_degree (m : GiantSignedMemory PB) (b : B → ℕ)
    (deleted : (g : B) → Finset (Fin (m.1 g)))
    (born : (g : B) → Fin (b g) → PB g) (g : B) :
    (giantSignedFixedGhostTarget m b deleted born).1 g =
      m.1 g - (deleted g).card + b g := by
  exact giantSignedGhostTarget_degree ⟨m.1 g, m.2 g⟩ (deleted g) (born g)

structure GiantSignedChronologicalChoices (PS : S → Finset ℕ) (PB : B → Finset ℕ)
    {k n : ℕ} (ell : ℕ) (C : Fin n → B → Finset (Fin k))
    (batch : Fin (n+1) → B → ℕ) where
  state : Fin (n+1) → GiantSignedState PS PB (k+ell)
  deleted : (i : Fin (n+1)) → (g : B) → Finset (Fin ((state i).2.2.1 g))
  born : (i : Fin (n+1)) → (g : B) → Fin (batch i g) → PB g
  sourceSmallPermutation : Fin n → (g : S) → Equiv.Perm (Fin (k+ell))
  targetSmallPermutation : Fin n → (g : S) → Equiv.Perm (Fin (k+ell))
  sourceBigPermutation : Fin n → (g : B) → Equiv.Perm (Fin (k+ell))
  targetBigPermutation : Fin n → (g : B) → Equiv.Perm (Fin (k+ell))
  auxiliary : (i : Fin n) → GiantTwoSidedPatternAuxiliary PB (C i)
  edge : (i : Fin n) → GiantSignedEdgeChoice (fun g => ell + (C i g).card)
    (giantSignedFixedGhostTarget (state i.castSucc).2.2 (batch i.castSucc)
      (deleted i.castSucc) (born i.castSucc)).1

variable {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}

def giantSignedChronologicalGhostTarget
    (h : GiantSignedChronologicalChoices PS PB ell C batch) (i : Fin (n+1)) :
    GiantSignedMemory PB :=
  giantSignedFixedGhostTarget (h.state i).2.2 (batch i) (h.deleted i) (h.born i)

def giantSignedChronologicalAfterVisitState
    (h : GiantSignedChronologicalChoices PS PB ell C batch) (i : Fin (n+1)) :
    GiantSignedState PS PB (k+ell) :=
  ((h.state i).1, (h.state i).2.1, giantSignedChronologicalGhostTarget h i)

def giantSignedChronologicalSmallSource
    (h : GiantSignedChronologicalChoices PS PB ell C batch) (i : Fin n) :
    GiantTwoSidedResidueState PS (k+ell) :=
  giantTwoSidedResiduePermute (h.sourceSmallPermutation i) (h.state i.castSucc).1

def giantSignedChronologicalSmallTarget
    (h : GiantSignedChronologicalChoices PS PB ell C batch) (i : Fin n) :
    GiantTwoSidedResidueState PS (k+ell) :=
  giantTwoSidedResiduePermute (h.targetSmallPermutation i) (h.state i.succ).1

def giantSignedChronologicalBigSource
    (h : GiantSignedChronologicalChoices PS PB ell C batch) (i : Fin n) :
    MarkedPhysicalMarking PB (k+ell) :=
  fun g s => (h.state i.castSucc).2.1 g (h.sourceBigPermutation i g s)

def giantSignedChronologicalBigTarget
    (h : GiantSignedChronologicalChoices PS PB ell C batch) (i : Fin n) :
    MarkedPhysicalMarking PB (k+ell) :=
  fun g s => (h.state i.succ).2.1 g (h.targetBigPermutation i g s)

def giantSignedChronologicalBirthData
    (h : GiantSignedChronologicalChoices PS PB ell C batch) : GiantSignedBirthData PB ell C batch where
  initial := (h.state 0).2.1
  target := giantSignedChronologicalBigTarget h
  promoted := fun i => (h.edge i).2.1
  born := h.born

theorem giantSignedChronologicalBirthValue_initial
    (h : GiantSignedChronologicalChoices PS PB ell C batch) (g : B) (s : Fin (k+ell)) :
    giantSignedBirthValue (giantSignedChronologicalBirthData h) (.inl ⟨g,s⟩) =
      some ((h.state 0).2.1 g s).val := rfl

theorem giantSignedChronologicalBirthValue_fresh
    (h : GiantSignedChronologicalChoices PS PB ell C batch) (i : Fin n) (g : B)
    (s : Fin (ell + (C i g).card)) (hs : s ∉ (h.edge i).2.1 g) :
    giantSignedBirthValue (giantSignedChronologicalBirthData h) (.inr (.inl ⟨i,g,s⟩)) =
      some (giantSignedPatternFreeLabels (C i) (giantSignedChronologicalBigTarget h i) g s).val :=
  ite_eq_right hs

theorem giantSignedChronologicalBirthValue_promoted
    (h : GiantSignedChronologicalChoices PS PB ell C batch) (i : Fin n) (g : B)
    (s : Fin (ell + (C i g).card)) (hs : s ∈ (h.edge i).2.1 g) :
    giantSignedBirthValue (giantSignedChronologicalBirthData h) (.inr (.inl ⟨i,g,s⟩)) = none :=
  ite_eq_left hs

theorem giantSignedChronologicalBirthValue_ghost
    (h : GiantSignedChronologicalChoices PS PB ell C batch) (i : Fin (n+1)) (g : B)
    (s : Fin (batch i g)) :
    giantSignedBirthValue (giantSignedChronologicalBirthData h) (.inr (.inr ⟨i,g,s⟩)) =
      some (h.born i g s).val := rfl

theorem giantSignedChronologicalGhostTarget_born
    (h : GiantSignedChronologicalChoices PS PB ell C batch) (i : Fin (n+1)) (g : B)
    (s : Fin (batch i g)) :
    (giantSignedChronologicalGhostTarget h i).2 g
        (Fin.natAdd ((h.deleted i g)ᶜ).card s) = ⟨h.born i g s, 0⟩ := by
  exact giantSignedGhostTarget_born ⟨(h.state i).2.2.1 g, (h.state i).2.2.2 g⟩
    (h.deleted i g) (h.born i g) s

end
end ArtinMatthews
