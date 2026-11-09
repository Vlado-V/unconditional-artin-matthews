module

public import ArtinMatthews.GiantSignedLifespanPathData


set_option backward.privateInPublic true
@[expose] public section

/-! The original fixed-pattern label path and its small root coordinates.
The full integer offsets come from the original signed dilation. -/

namespace ArtinMatthews
open Finset
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B]
    (PS : S → Finset ℕ) (PB : B → Finset ℕ) {k ell n : ℕ}
    (C : Fin n → B → Finset (Fin k)) (κ : Fin n → ℤ)

local notation "Bands" => Sum.elim PS PB
local notation "Pattern" => giantSignedChronologicalJoinedPattern (S := S) C

structure GiantSignedLifespanOriginalPath where
  labels : Fin (n+1) → MarkedPhysicalMarking Bands (k+ell)
  sourcePermutation : Fin n → S ⊕ B → Equiv.Perm (Fin (k+ell))
  targetPermutation : Fin n → S ⊕ B → Equiv.Perm (Fin (k+ell))
  auxiliary : ∀ i, GiantTwoSidedPatternAuxiliary Bands (Pattern i)
  static : GiantTwoSidedStaticLabels Pattern sourcePermutation targetPermutation auxiliary labels
  compatible : GiantTwoSidedActiveCompatible univ labels
    (giantTwoSidedPathOffset (giantTwoSidedLabelIncrement Pattern labels sourcePermutation auxiliary κ))
  smallRoot : GiantTwoSidedFullResidue PS
  smallHits : ∀ (i : Fin (n+1)) (g : S) (j : Fin (k+ell)), giantTwoSidedResidueTranslate (P := PS)
    (giantTwoSidedPathOffset (giantTwoSidedLabelIncrement Pattern labels sourcePermutation auxiliary κ) i)
    smallRoot (giantTwoSidedResidueIndex (P := PS) g (labels i (Sum.inl g : S ⊕ B) j)) = 0

namespace GiantSignedLifespanOriginalPath

variable {PS PB C κ} (path : GiantSignedLifespanOriginalPath PS PB (ell := ell) C κ)

def increment : Fin n → ℤ :=
  giantTwoSidedLabelIncrement (ell := ell) Pattern path.labels path.sourcePermutation path.auxiliary κ

def offset : Fin (n+1) → ℤ := giantTwoSidedPathOffset path.increment

def visits (g : B) (p : PB g) : Finset (Fin (n+1)) :=
  giantSignedActualActiveVisits (J := S ⊕ B) (PB := Bands) path.labels p.val

def smallState (i : Fin (n+1)) : GiantTwoSidedResidueState PS (k+ell) :=
  giantSignedLifespanSmallState (fun g j => path.labels i (Sum.inl g : S ⊕ B) j)
    path.smallRoot (path.offset i) (fun g => path.static.1 i (Sum.inl g : S ⊕ B)) (path.smallHits i)

variable {q : Fin (n+1) → ℝ} {c : ∀ g p, GiantSignedResidueLifespanChoice (path.visits g p)}

def schedule (hP : ∀ (g : S ⊕ B) p, p ∈ Bands g → p.Prime)
    (hdis : Pairwise (fun i j : S ⊕ B => Disjoint (Bands i) (Bands j)))
    (hκ : ∀ i, 0 < (κ i).natAbs) (hsize : ∀ i g p, p ∈ Bands g → (κ i).natAbs < p)
    (hw : ∀ g p, giantSignedResidueLifespanWeight p.val path.offset q (path.visits g p) (c g p) ≠ 0)
    (order : ∀ v g, Fin (giantSignedGhostVisitBorn (c g) v).card ≃ ↥(giantSignedGhostVisitBorn (c g) v)) :
    GiantSignedLifespanScheduleData (A := path.visits) c path.offset q (fun i g => ell+(C i g).card) :=
  giantSignedLifespanPathSchedule path.labels path.sourcePermutation path.targetPermutation path.auxiliary κ
    hP hdis hκ hsize path.static path.compatible q c hw order

variable (data : GiantSignedLifespanScheduleData (A := path.visits) c path.offset q (fun i g => ell+(C i g).card))

def chronology : GiantSignedChronologicalChoices PS PB ell C data.batch :=
  giantSignedChronologyFromSchedule data path.smallState (fun i g j => path.labels i (Sum.inr g : S ⊕ B) j)
    (fun i g => path.sourcePermutation i (Sum.inl g : S ⊕ B))
    (fun i g => path.targetPermutation i (Sum.inl g : S ⊕ B))
    (fun i g => path.sourcePermutation i (Sum.inr g : S ⊕ B))
    (fun i g => path.targetPermutation i (Sum.inr g : S ⊕ B))
    (fun i g => path.auxiliary i (Sum.inr g : S ⊕ B))

theorem chronology_labels : giantSignedChronologicalJoinedLabels (path.chronology data) = path.labels := by
  funext i g
  cases g <;> rfl

theorem chronology_sourcePermutation :
    giantSignedChronologicalJoinedSourcePermutation (path.chronology data) = path.sourcePermutation := by
  funext i g
  cases g <;> rfl

theorem chronology_targetPermutation :
    giantSignedChronologicalJoinedTargetPermutation (path.chronology data) = path.targetPermutation := by
  funext i g
  cases g <;> rfl

theorem chronology_auxiliary :
    giantSignedChronologicalJoinedAuxiliary (path.chronology data) = path.auxiliary := by
  funext i g a
  cases g with
  | inl g => exact (notMem_empty a.val a.property).elim
  | inr g => rfl

theorem chronology_increment (i : Fin n) :
    κ i * (giantSignedChronologicalProduct (path.chronology data) i : ℤ) = path.increment i := by
  rw [← giantSignedChronologicalJoinedIncrement_eq (path.chronology data) κ i,chronology_labels,
    chronology_sourcePermutation,chronology_auxiliary]
  rfl

theorem chronology_product (i : Fin n) :
    giantSignedChronologicalProduct (path.chronology data) i = giantTwoSidedPatternDilation (Pattern i)
      (giantTwoSidedPermuteLabels (path.sourcePermutation i) (path.labels i.castSucc)) (path.auxiliary i) := by
  rw [← giantSignedChronologicalJoinedDilation_eq (path.chronology data) i,chronology_labels,
    chronology_sourcePermutation,chronology_auxiliary]

theorem chronology_offset : giantSignedChronologicalJoinedOffset (path.chronology data) κ = path.offset := by
  rw [giantSignedChronologicalJoinedOffset,chronology_labels,chronology_sourcePermutation,chronology_auxiliary]
  rfl

end GiantSignedLifespanOriginalPath
end
end ArtinMatthews
