module

public import ArtinMatthews.GiantTwoSidedRootLabelData


set_option backward.privateInPublic true
@[expose] public section

/-! Encode a physical path by its original root and full ordered label
array. The inverse reconstructs every visited state from the signed
increments, giving a finite bijection with all slice guards retained. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def giantTwoSidedRootLabel_encode {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k ell n : ℕ} {C : Fin n → J → Finset (Fin k)}
    {π τ : Fin n → J → Equiv.Perm (Fin (k+ell))}
    {aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)} {step : Fin n → ℤ} {I Z : Finset ℕ}
    (s : GiantTwoSidedPhysicalPath C π τ aux step I Z) : GiantTwoSidedRootLabelPath C π τ aux step I Z := by
  let d : GiantTwoSidedRootLabelData (P:=P) k ell n I :=
    (⟨(s.val 0).val.1.val,s.property.root_mem⟩,fun v => (s.val v).val.2)
  have hpos (v : Fin (n+1)) : giantTwoSidedRootLabelPosition C π aux step d v =
      ((s.val v).val.1.val:ℤ) :=
    (giantTwoSidedPatternPath_position s.val π τ aux step s.property.edges v).symm
  refine ⟨d,⟨fun v => (s.val v).property.1,?_,?_,?_,?_⟩⟩
  · intro i
    exact ⟨(s.property.edges i).1,(s.property.edges i).2.2⟩
  · intro v
    rw [hpos]
    exact Int.natCast_nonneg _
  · intro v
    rw [hpos,Int.toNat_natCast]
    exact (s.val v).val.1.property
  · intro v j l
    rw [hpos]
    exact Int.natCast_dvd_natCast.mpr ((s.val v).property.2 j l)

theorem giantTwoSidedRootLabel_encode_position {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k ell n : ℕ} {C : Fin n → J → Finset (Fin k)}
    {π τ : Fin n → J → Equiv.Perm (Fin (k+ell))}
    {aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)} {step : Fin n → ℤ} {I Z : Finset ℕ}
    (s : GiantTwoSidedPhysicalPath C π τ aux step I Z) (v : Fin (n+1)) :
    giantTwoSidedRootLabelPosition C π aux step (giantTwoSidedRootLabel_encode s).val v =
      ((s.val v).val.1.val:ℤ) :=
  (giantTwoSidedPatternPath_position s.val π τ aux step s.property.edges v).symm

def giantTwoSidedRootLabel_decode {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k ell n : ℕ} {C : Fin n → J → Finset (Fin k)}
    {π τ : Fin n → J → Equiv.Perm (Fin (k+ell))}
    {aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)} {step : Fin n → ℤ} {I Z : Finset ℕ}
    (d : GiantTwoSidedRootLabelPath C π τ aux step I Z) : GiantTwoSidedPhysicalPath C π τ aux step I Z :=
  ⟨giantTwoSidedRootLabel_reconstruct d,giantTwoSidedRootLabel_reconstruct_condition d⟩

def giantTwoSidedRootLabelEquiv {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k ell n : ℕ} (C : Fin n → J → Finset (Fin k))
    (π τ : Fin n → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ) (I Z : Finset ℕ) :
    GiantTwoSidedPhysicalPath C π τ aux step I Z ≃ GiantTwoSidedRootLabelPath C π τ aux step I Z where
  toFun := giantTwoSidedRootLabel_encode
  invFun := giantTwoSidedRootLabel_decode
  left_inv s := by
    apply Subtype.ext
    funext v
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      apply Int.ofNat.inj
      exact (giantTwoSidedRootLabel_reconstruct_position (giantTwoSidedRootLabel_encode s) v).trans
        (giantTwoSidedRootLabel_encode_position s v)
    · rfl
  right_inv d := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      apply Int.ofNat.inj
      change ((giantTwoSidedRootLabel_reconstruct d 0).val.1.val:ℤ)=(d.val.1.val:ℤ)
      rw [giantTwoSidedRootLabel_reconstruct_position,giantTwoSidedRootLabelPosition,
        giantTwoSidedPathOffset_zero,add_zero]
    · rfl

theorem giantTwoSidedRootLabel_sum {J A : Type*} [Fintype J] [DecidableEq J] [AddCommMonoid A]
    {P : J → Finset ℕ} {k ell n : ℕ} (C : Fin n → J → Finset (Fin k))
    (π τ : Fin n → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ) (I Z : Finset ℕ)
    (f : GiantTwoSidedRootLabelPath C π τ aux step I Z → A) :
    (∑ s : GiantTwoSidedPhysicalPath C π τ aux step I Z,f (giantTwoSidedRootLabel_encode s)) =
      ∑ d : GiantTwoSidedRootLabelPath C π τ aux step I Z,f d :=
  (giantTwoSidedRootLabelEquiv C π τ aux step I Z).sum_comp f

end
end ArtinMatthews
