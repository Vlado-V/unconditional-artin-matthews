module

public import ArtinMatthews.GiantSignedBirthChronology


set_option backward.privateInPublic true
@[expose] public section

/-! The initial slots, ordered ghost batch and fresh edge slots are
literal embeddings into the common potential-address frame. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

universe u
variable {B : Type u} {M n H k ell : ℕ}

def giantSignedInitialBirthDraw : (Σ _ : B, Fin M) ↪ GiantSignedUniformBirthAddress B M n H where
  toFun a := .inl (a.1,a.2)
  inj' := by
    rintro ⟨g,i⟩ ⟨h,j⟩ he
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Sum.inl.inj he)
    rfl

def giantSignedVisitBirthDraw (i : Fin (n+1)) (b : B → ℕ) (hb : ∀ g, b g ≤ H) :
    (Σ g : B, Fin (b g)) ↪ GiantSignedUniformBirthAddress B M n H where
  toFun a := .inr (.inr ⟨i,a.1,⟨a.2.val,a.2.isLt.trans_le (hb a.1)⟩⟩)
  inj' := by
    rintro ⟨g,j⟩ ⟨h,l⟩ he
    have hs := eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr.inj (Sum.inr.inj he))).2
    obtain ⟨rfl,hh⟩ := Sigma.mk.inj_iff.mp hs
    have hj : j = l := Fin.ext (congrArg (fun i : Fin H => i.val) (eq_of_heq hh))
    cases hj
    rfl

def giantSignedEdgeBirthDraw (i : Fin n) (C : B → Finset (Fin k))
    (promoted : (g : B) → Finset (Fin (ell+(C g).card))) :
    (Σ g : B, {j : Fin (ell+(C g).card) // j ∉ promoted g}) ↪
      GiantSignedUniformBirthAddress B (k+ell) n H where
  toFun a := .inr (.inl ⟨i,a.1,giantSignedFreeSlotEmbedding (C a.1) ell a.2.val⟩)
  inj' := by
    rintro ⟨g,j⟩ ⟨h,l⟩ he
    have hs := eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inl.inj (Sum.inr.inj he))).2
    obtain ⟨rfl,hh⟩ := Sigma.mk.inj_iff.mp hs
    have hj : j = l := Subtype.ext ((giantSignedFreeSlotEmbedding (C g) ell).injective (eq_of_heq hh))
    cases hj
    rfl

variable {PB : B → Finset ℕ} {C : Fin n → B → Finset (Fin k)}
    {batch : Fin (n+1) → B → ℕ}

def GiantSignedBirthStageDraw (d : GiantSignedBirthData PB ell C batch) :
    GiantSignedBirthOperation n → Type u
  | .initial => Σ _ : B, Fin (k+ell)
  | .visit i => Σ g : B, Fin (batch i g)
  | .edge i => Σ g : B, {j : Fin (ell+(C i g).card) // j ∉ d.promoted i g}

instance giantSignedBirthStageDraw_fintype [Fintype B]
    (d : GiantSignedBirthData PB ell C batch) (o : GiantSignedBirthOperation n) :
    Fintype (GiantSignedBirthStageDraw d o) := by
  cases o <;> unfold GiantSignedBirthStageDraw <;> infer_instance

def giantSignedBirthStageEmbedding (d : GiantSignedBirthData PB ell C batch)
    (hH : ∀ i g, batch i g ≤ H) :
    (o : GiantSignedBirthOperation n) → GiantSignedBirthStageDraw d o ↪
      GiantSignedUniformBirthAddress B (k+ell) n H
  | .initial => giantSignedInitialBirthDraw
  | .visit i => giantSignedVisitBirthDraw i (batch i) (hH i)
  | .edge i => giantSignedEdgeBirthDraw i (C i) (d.promoted i)

def giantSignedBirthStagePrime (d : GiantSignedBirthData PB ell C batch) :
    (o : GiantSignedBirthOperation n) → GiantSignedBirthStageDraw d o → ℕ
  | .initial, a => (d.initial a.1 a.2).val
  | .visit i, a => (d.born i a.1 a.2).val
  | .edge i, a => (giantSignedPatternFreeLabels (C i) (d.target i) a.1 a.2.val).val

def giantSignedBirthStageTuple (d : GiantSignedBirthData PB ell C batch)
    (hH : ∀ i g, batch i g ≤ H) (o : GiantSignedBirthOperation n)
    (a : GiantSignedBirthStageDraw d o) :
    PB (giantSignedUniformBirthGroup (giantSignedBirthStageEmbedding d hH o a)) := by
  cases o with
  | initial => exact d.initial a.1 a.2
  | visit i => exact d.born i a.1 a.2
  | edge i => exact giantSignedPatternFreeLabels (C i) (d.target i) a.1 a.2.val

theorem giantSignedBirthStageTuple_value (d : GiantSignedBirthData PB ell C batch)
    (hH : ∀ i g, batch i g ≤ H) (o : GiantSignedBirthOperation n)
    (a : GiantSignedBirthStageDraw d o) :
    (giantSignedBirthStageTuple d hH o a).val = giantSignedBirthStagePrime d o a := by
  cases o <;> rfl

theorem giantSignedBirthStageEmbedding_operation (d : GiantSignedBirthData PB ell C batch)
    (hH : ∀ i g, batch i g ≤ H) (o : GiantSignedBirthOperation n)
    (a : GiantSignedBirthStageDraw d o) :
    giantSignedUniformBirthOperation (k+ell) n H (giantSignedBirthStageEmbedding d hH o a) = o := by
  cases o <;> rfl

theorem giantSignedBirthStageEmbedding_value (d : GiantSignedBirthData PB ell C batch)
    (hH : ∀ i g, batch i g ≤ H) (o : GiantSignedBirthOperation n)
    (a : GiantSignedBirthStageDraw d o) :
    giantSignedUniformBirthValue d H hH (giantSignedBirthStageEmbedding d hH o a) =
      some (giantSignedBirthStagePrime d o a) := by
  cases o with
  | initial => exact giantSignedUniformBirthValue_initial d H hH a.1 a.2
  | visit i => exact giantSignedUniformBirthValue_ghost d H hH i a.1 a.2
  | edge i => exact giantSignedUniformBirthValue_fresh d H hH i a.1 a.2.val a.2.property

theorem giantSignedBirthStageEmbedding_range (d : GiantSignedBirthData PB ell C batch)
    (hH : ∀ i g, batch i g ≤ H) (o : GiantSignedBirthOperation n)
    (a : GiantSignedUniformBirthAddress B (k+ell) n H) :
    a ∈ Set.range (giantSignedBirthStageEmbedding d hH o) ↔
      giantSignedUniformBirthOperation (k+ell) n H a = o ∧ giantSignedUniformBirthValue d H hH a ≠ none := by
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨giantSignedBirthStageEmbedding_operation d hH o x,
      (giantSignedBirthStageEmbedding_value d hH o x).trans_ne (Option.some_ne_none _)⟩
  · rintro ⟨ho, hv⟩
    obtain ⟨x,hx⟩ := giantSignedUniformBirthValue_covers d H hH a hv
    subst a
    rcases x with ⟨g,j⟩ | ⟨i,g,j⟩ | ⟨i,g,j⟩
    · change GiantSignedBirthOperation.initial = o at ho
      subst o
      exact ⟨⟨g,j⟩,rfl⟩
    · change GiantSignedBirthOperation.edge i = o at ho
      subst o
      exact ⟨⟨g,j⟩,rfl⟩
    · change GiantSignedBirthOperation.visit i = o at ho
      subst o
      exact ⟨⟨g,j⟩,rfl⟩

end
end ArtinMatthews
