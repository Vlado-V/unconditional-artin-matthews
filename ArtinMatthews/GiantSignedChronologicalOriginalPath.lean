module

public import ArtinMatthews.GiantSignedLifespanOriginalPath
public import ArtinMatthews.GiantSignedChronologicalDecodedLifespans


set_option backward.privateInPublic true
@[expose] public section

/-! Recover the literal fixed-pattern path and its initial small root
from a birth-distinct chronology. The recovery uses the full dilation. -/

namespace ArtinMatthews
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}
    (h : GiantSignedChronologicalChoices PS PB ell C batch) (κ : Fin n → ℤ)

def giantSignedChronologicalOriginalPath (ha : GiantSignedChronologicalAdmissible κ h)
    (hd : GiantSignedBirthDistinct (giantSignedChronologicalBirthData h))
    (hSB : ∀ s b, Disjoint (PS s) (PB b)) : GiantSignedLifespanOriginalPath PS PB (ell := ell) C κ where
  labels := giantSignedChronologicalJoinedLabels h
  sourcePermutation := giantSignedChronologicalJoinedSourcePermutation h
  targetPermutation := giantSignedChronologicalJoinedTargetPermutation h
  auxiliary := giantSignedChronologicalJoinedAuxiliary h
  static := giantSignedChronologicalJoinedStaticLabels_of_birthDistinct h κ ha hd
  compatible := giantSignedChronologicalJoinedActiveCompatible h κ ha hd hSB
  smallRoot := (h.state 0).1.val.1
  smallHits i g j := by
    let p := giantTwoSidedResidueIndex g ((h.state i).1.val.2 g j)
    have he := congrArg (fun r : GiantTwoSidedFullResidue PS => r p)
      (giantSignedChronologicalSmallResidue_eq_translate h κ ha.compatible i)
    exact he.symm.trans ((h.state i).1.property.2 g j)

def giantSignedChronologicalRecoveredBirthOrders (q : Fin (n+1) → ℝ)
    (d : GiantSignedChronologicalDecodedLifespans h κ q) (i : Fin (n+1)) (g : B) :
    Fin (giantSignedGhostVisitBorn (d.choice g) i).card ≃ ↥(giantSignedGhostVisitBorn (d.choice g) i) :=
  (d.coefficientData.ghostMatch i g).choose

theorem giantSignedChronologicalRecoveredBirthOrders_move (q : Fin (n+1) → ℝ)
    (d : GiantSignedChronologicalDecodedLifespans h κ q) (i : Fin (n+1)) (g : B) :
    giantSignedFixedGhostMove (h.state i).2.2 (batch i) (h.deleted i) (h.born i) g =
      giantSignedGhostVisitMove (d.choice g) i (giantSignedMemoryGroupEquiv PB (h.state i).2.2 g)
        (giantSignedChronologicalRecoveredBirthOrders h κ q d i g) :=
  (d.coefficientData.ghostMatch i g).choose_spec

end
end ArtinMatthews
