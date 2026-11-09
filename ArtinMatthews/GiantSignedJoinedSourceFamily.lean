module

public import ArtinMatthews.GiantTwoSidedPatternKernel
public import ArtinMatthews.GiantCandidateGroups


set_option backward.privateInPublic true
@[expose] public section

/-! The source uses empty exceptional copied sets on the small groups.
The original scalar coefficient reads the ordered big coordinates. -/
namespace ArtinMatthews
noncomputable section

def giantSignedJoinedPattern {S B : Type*} {k : ℕ} (C : B → Finset (Fin k)) :
    S ⊕ B → Finset (Fin k) :=
  Sum.elim (fun _ => ∅) C

def giantSignedJoinedCoefficient {S B : Type*} {PS : S → Finset ℕ} {PB : B → Finset ℕ}
    {k ell : ℕ} {C : B → Finset (Fin k)} (K : GiantTwoSidedPatternCoefficient PB C ell) :
    GiantTwoSidedPatternCoefficient (Sum.elim PS PB) (giantSignedJoinedPattern C) ell :=
  fun a b aux => K (fun g => a (.inr g)) (fun g => b (.inr g)) (fun g => aux (.inr g))

variable {x : ℝ} (groups : Finset (GiantCandidateGroupIndex x))

abbrev GiantCandidatePerformedSmall :=
  {i : GiantCandidateSmallGroupIndex x // Sum.inl i ∈ groups}

abbrev GiantCandidatePerformedBig :=
  {g : GiantCandidateBigGroupIndex x // Sum.inr g ∈ groups}

def giantCandidatePerformedSplitEquiv :
    GiantCandidatePerformedSmall groups ⊕ GiantCandidatePerformedBig groups ≃ ↥groups where
  toFun := fun
    | .inl i => ⟨.inl i.val, i.property⟩
    | .inr g => ⟨.inr g.val, g.property⟩
  invFun := fun
    | ⟨.inl i, hi⟩ => .inl ⟨i,hi⟩
    | ⟨.inr g, hg⟩ => .inr ⟨g,hg⟩
  left_inv := by rintro (⟨i,hi⟩ | ⟨g,hg⟩) <;> rfl
  right_inv := by rintro ⟨i | g, h⟩ <;> rfl

def giantCandidatePerformedSmallBand (i : GiantCandidatePerformedSmall groups) : Finset ℕ :=
  giantCandidateSmallGroup x i.val

def giantCandidatePerformedBigBand (g : GiantCandidatePerformedBig groups) : Finset ℕ :=
  giantCandidateBigGroup x g.val

theorem giantCandidatePerformedSplit_band
    (i : GiantCandidatePerformedSmall groups ⊕ GiantCandidatePerformedBig groups) :
    Sum.elim (giantCandidatePerformedSmallBand groups) (giantCandidatePerformedBigBand groups) i =
      giantCandidateGroup x (giantCandidatePerformedSplitEquiv groups i).val := by
  cases i <;> rfl

def giantCandidatePerformedPattern {k : ℕ}
    (C : GiantCandidatePerformedBig groups → Finset (Fin k)) : ↥groups → Finset (Fin k) :=
  fun
    | ⟨.inl _, _⟩ => ∅
    | ⟨.inr g, hg⟩ => C ⟨g,hg⟩

theorem giantCandidatePerformedSplit_pattern {k : ℕ}
    (C : GiantCandidatePerformedBig groups → Finset (Fin k))
    (i : GiantCandidatePerformedSmall groups ⊕ GiantCandidatePerformedBig groups) :
    giantSignedJoinedPattern C i =
      giantCandidatePerformedPattern groups C (giantCandidatePerformedSplitEquiv groups i) := by
  cases i <;> rfl

def giantCandidatePerformedCoefficient {k ell : ℕ}
    {C : GiantCandidatePerformedBig groups → Finset (Fin k)}
    (K : GiantTwoSidedPatternCoefficient (giantCandidatePerformedBigBand groups) C ell) :
    GiantTwoSidedPatternCoefficient (fun i : ↥groups => giantCandidateGroup x i.val)
      (giantCandidatePerformedPattern groups C) ell :=
  fun a b aux => K (fun g => a (giantCandidatePerformedSplitEquiv groups (.inr g)))
    (fun g => b (giantCandidatePerformedSplitEquiv groups (.inr g)))
    (fun g => aux (giantCandidatePerformedSplitEquiv groups (.inr g)))

def giantCandidatePerformedSmallUnivEquiv (x : ℝ) :
    GiantCandidatePerformedSmall (Finset.univ : Finset (GiantCandidateGroupIndex x)) ≃
      GiantCandidateSmallGroupIndex x where
  toFun := Subtype.val
  invFun i := ⟨i,Finset.mem_univ _⟩
  left_inv _ := rfl
  right_inv _ := rfl

def giantCandidatePerformedBigUnivEquiv (x : ℝ) :
    GiantCandidatePerformedBig (Finset.univ : Finset (GiantCandidateGroupIndex x)) ≃
      GiantCandidateBigGroupIndex x where
  toFun := Subtype.val
  invFun i := ⟨i,Finset.mem_univ _⟩
  left_inv _ := rfl
  right_inv _ := rfl

end
end ArtinMatthews
