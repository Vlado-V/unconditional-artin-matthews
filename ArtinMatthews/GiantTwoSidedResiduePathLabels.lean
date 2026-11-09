module

public import ArtinMatthews.GiantTwoSidedResiduePatternKernel
public import ArtinMatthews.GiantTwoSidedRootWeight


set_option backward.privateInPublic true
@[expose] public section

/-! A full residue path is equivalent to its initial residue tuple and
all its ordered labels, with the exact signed offsets at each visit. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantTwoSidedResidueTranslate_zero {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (r : GiantTwoSidedFullResidue P) :
    giantTwoSidedResidueTranslate 0 r=r := by
  funext p
  simp [giantTwoSidedResidueTranslate]

theorem giantTwoSidedResidueTranslate_add {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (h k : ℤ) (r : GiantTwoSidedFullResidue P) :
    giantTwoSidedResidueTranslate (h+k) r=
      giantTwoSidedResidueTranslate k (giantTwoSidedResidueTranslate h r) := by
  funext p
  simp [giantTwoSidedResidueTranslate,add_assoc]

abbrev GiantTwoSidedResiduePath {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k ell n : ℕ} (C : Fin n → J → Finset (Fin k))
    (π τ : Fin n → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ) :=
  {s : Fin (n+1) → GiantTwoSidedResidueState P (k+ell) //
    ∀ i,GiantTwoSidedResiduePatternCondition (C i) (step i)
      (giantTwoSidedResiduePermute (π i) (s i.castSucc))
      (giantTwoSidedResiduePermute (τ i) (s i.succ)) (aux i)}

abbrev GiantTwoSidedResidueRootData {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (k ell n : ℕ) :=
  GiantTwoSidedFullResidue P × (Fin (n+1) → MarkedPhysicalMarking P (k+ell))

def giantTwoSidedResidueRootPosition {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k ell n : ℕ} (C : Fin n → J → Finset (Fin k))
    (π : Fin n → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ)
    (d : GiantTwoSidedResidueRootData P k ell n) (v : Fin (n+1)) : GiantTwoSidedFullResidue P :=
  giantTwoSidedResidueTranslate
    (giantTwoSidedPathOffset (giantTwoSidedLabelIncrement C d.2 π aux step) v) d.1

structure GiantTwoSidedResidueRootCondition {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k ell n : ℕ} (C : Fin n → J → Finset (Fin k))
    (π τ : Fin n → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ)
    (d : GiantTwoSidedResidueRootData P k ell n) : Prop where
  distinct : ∀ v,MarkedPhysicalMarkingDistinct (d.2 v)
  compatible : ∀ i,GiantTwoSidedLabelCompatible (C i)
    (giantTwoSidedPermuteLabels (π i) (d.2 i.castSucc))
    (giantTwoSidedPermuteLabels (τ i) (d.2 i.succ)) (aux i)
  active : ∀ v j l,giantTwoSidedResidueRootPosition C π aux step d v
    (giantTwoSidedResidueIndex j (d.2 v j l))=0

abbrev GiantTwoSidedResidueRootPath {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k ell n : ℕ} (C : Fin n → J → Finset (Fin k))
    (π τ : Fin n → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ) :=
  {d : GiantTwoSidedResidueRootData P k ell n // GiantTwoSidedResidueRootCondition C π τ aux step d}

theorem giantTwoSidedResiduePath_position {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k ell n : ℕ} {C : Fin n → J → Finset (Fin k)}
    {π τ : Fin n → J → Equiv.Perm (Fin (k+ell))}
    {aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)} {step : Fin n → ℤ}
    (s : GiantTwoSidedResiduePath C π τ aux step) (v : Fin (n+1)) :
    (s.val v).val.1=giantTwoSidedResidueRootPosition C π aux step
      ((s.val 0).val.1,fun w => (s.val w).val.2) v := by
  refine Fin.induction ?_ ?_ v
  · rw [giantTwoSidedResidueRootPosition,giantTwoSidedPathOffset_zero,giantTwoSidedResidueTranslate_zero]
  · intro i ih
    have hs := (s.property i).2.1
    change (s.val i.succ).val.1=giantTwoSidedResidueTranslate
      (giantTwoSidedLabelIncrement C (fun w => (s.val w).val.2) π aux step i) (s.val i.castSucc).val.1 at hs
    rw [hs,ih]
    unfold giantTwoSidedResidueRootPosition
    rw [giantTwoSidedPathOffset_succ,giantTwoSidedResidueTranslate_add]

def giantTwoSidedResidueRoot_encode {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k ell n : ℕ} {C : Fin n → J → Finset (Fin k)}
    {π τ : Fin n → J → Equiv.Perm (Fin (k+ell))}
    {aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)} {step : Fin n → ℤ}
    (s : GiantTwoSidedResiduePath C π τ aux step) : GiantTwoSidedResidueRootPath C π τ aux step := by
  refine ⟨((s.val 0).val.1,fun v => (s.val v).val.2),⟨fun v => (s.val v).property.1,?_,?_⟩⟩
  · intro i
    exact ⟨(s.property i).1,(s.property i).2.2⟩
  · intro v j l
    rw [← giantTwoSidedResiduePath_position s v]
    exact (s.val v).property.2 j l

def giantTwoSidedResidueRoot_reconstruct {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k ell n : ℕ} {C : Fin n → J → Finset (Fin k)}
    {π τ : Fin n → J → Equiv.Perm (Fin (k+ell))}
    {aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)} {step : Fin n → ℤ}
    (d : GiantTwoSidedResidueRootPath C π τ aux step) (v : Fin (n+1)) :
    GiantTwoSidedResidueState P (k+ell) :=
  ⟨(giantTwoSidedResidueRootPosition C π aux step d.val v,d.val.2 v),
    d.property.distinct v,d.property.active v⟩

theorem giantTwoSidedResidueRoot_reconstruct_condition {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k ell n : ℕ} {C : Fin n → J → Finset (Fin k)}
    {π τ : Fin n → J → Equiv.Perm (Fin (k+ell))}
    {aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)} {step : Fin n → ℤ}
    (d : GiantTwoSidedResidueRootPath C π τ aux step) :
    ∀ i,GiantTwoSidedResiduePatternCondition (C i) (step i)
      (giantTwoSidedResiduePermute (π i) (giantTwoSidedResidueRoot_reconstruct d i.castSucc))
      (giantTwoSidedResiduePermute (τ i) (giantTwoSidedResidueRoot_reconstruct d i.succ)) (aux i) := by
  intro i
  refine ⟨(d.property.compatible i).copied,?_,(d.property.compatible i).banned⟩
  change giantTwoSidedResidueRootPosition C π aux step d.val i.succ=
    giantTwoSidedResidueTranslate (giantTwoSidedLabelIncrement C d.val.2 π aux step i)
      (giantTwoSidedResidueRootPosition C π aux step d.val i.castSucc)
  unfold giantTwoSidedResidueRootPosition
  rw [giantTwoSidedPathOffset_succ,giantTwoSidedResidueTranslate_add]

def giantTwoSidedResidueRootEquiv {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k ell n : ℕ} (C : Fin n → J → Finset (Fin k))
    (π τ : Fin n → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ) :
    GiantTwoSidedResiduePath C π τ aux step ≃ GiantTwoSidedResidueRootPath C π τ aux step where
  toFun := giantTwoSidedResidueRoot_encode
  invFun d := ⟨giantTwoSidedResidueRoot_reconstruct d,giantTwoSidedResidueRoot_reconstruct_condition d⟩
  left_inv s := by
    apply Subtype.ext
    funext v
    apply Subtype.ext
    apply Prod.ext
    · exact (giantTwoSidedResiduePath_position s v).symm
    · rfl
  right_inv d := by
    apply Subtype.ext
    apply Prod.ext
    · change giantTwoSidedResidueRootPosition C π aux step d.val 0=d.val.1
      rw [giantTwoSidedResidueRootPosition,giantTwoSidedPathOffset_zero,giantTwoSidedResidueTranslate_zero]
    · rfl

end
end ArtinMatthews
