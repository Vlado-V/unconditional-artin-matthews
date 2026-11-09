module

public import ArtinMatthews.GiantSignedLifespanPathSchedule


set_option backward.privateInPublic true
@[expose] public section

/-! Insert the ordered memory schedule into the original chronological
states, leaving both active arrays and endpoint permutations literal. -/

namespace ArtinMatthews
noncomputable section

variable {S B : Type*} [Fintype S] {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {A : ∀ g, PB g → Finset (Fin (n+1))}
    {c : ∀ g p, GiantSignedResidueLifespanChoice (A g p)}
    {offset : Fin (n+1) → ℤ} {q : Fin (n+1) → ℝ}

def giantSignedChronologyFromSchedule
    (data : GiantSignedLifespanScheduleData c offset q (fun i g => ell+(C i g).card))
    (small : Fin (n+1) → GiantTwoSidedResidueState PS (k+ell))
    (active : Fin (n+1) → MarkedPhysicalMarking PB (k+ell))
    (πS τS : Fin n → S → Equiv.Perm (Fin (k+ell)))
    (πB τB : Fin n → B → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i, GiantTwoSidedPatternAuxiliary PB (C i)) :
    GiantSignedChronologicalChoices PS PB ell C data.batch where
  state v := (small v,active v,(data.memory v).1)
  deleted v := GiantSignedLifespanScheduleData.deleted v (data.memory v)
  born := data.born
  sourceSmallPermutation := πS
  targetSmallPermutation := τS
  sourceBigPermutation := πB
  targetBigPermutation := τB
  auxiliary := aux
  edge i := data.edge i (data.memory i.castSucc)

def giantSignedLifespanSmallState {M : ℕ} (labels : MarkedPhysicalMarking PS M)
    (root : GiantTwoSidedFullResidue PS) (d : ℤ)
    (hd : MarkedPhysicalMarkingDistinct labels)
    (hroot : ∀ j i, giantTwoSidedResidueTranslate (P := PS) d root (giantTwoSidedResidueIndex j (labels j i)) = 0) :
    GiantTwoSidedResidueState PS M :=
  ⟨(giantTwoSidedResidueTranslate (P := PS) d root,labels),⟨hd,hroot⟩⟩

end
end ArtinMatthews
