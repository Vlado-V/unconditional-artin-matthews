module

public import ArtinMatthews.IdealHeadAverages
public import ArtinMatthews.IdealPatternProducts
public import ArtinMatthews.IdealRawPattern


set_option backward.privateInPublic true
@[expose] public section

/-! All dilation and selected products are unchanged by passing to
the first-slot vector. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealCopiedProduct_head {G : Type*} [Fintype G]
    {P : G → Finset ℕ} {k ell : ℕ} (C : G → Finset (Fin k))
    (a : MarkedPhysicalMarking P (k+ell)) :
    giantTwoSidedPatternCopiedProduct C a=
      giantTwoSidedPatternCopiedProduct (ell:=0) C (idealLabelHead a) := by
  unfold giantTwoSidedPatternCopiedProduct
  apply prod_congr rfl
  intro g _
  apply prod_congr rfl
  intro i _
  rfl

theorem idealSelectedProduct_head {G : Type*} {P : G → Finset ℕ} {k ell : ℕ}
    (S : Finset (G × Fin k)) (a : MarkedPhysicalMarking P (k+ell)) :
    idealResidualSelectedMarking S a=idealFullSelectedLabels S (idealLabelHead a) := rfl

theorem idealCopiedProduct_fill {G : Type*} [Fintype G] [DecidableEq G]
    {P : G → Finset ℕ} {k : ℕ} (S : Finset (G × Fin k))
    (a : MarkedPhysicalMarking P k) (x : IdealSelectedLabels (idealResidualBands P S)) :
    giantTwoSidedPatternCopiedProduct (ell:=0) (idealResidualFreeSlots S) (idealSelectedFill S a x)=
      giantTwoSidedPatternCopiedProduct (ell:=0) (idealResidualFreeSlots S) a := by
  apply giantTwoSidedPatternCopiedProduct_eq
  intro g i hi
  have hn : (g,i)∉S := (mem_idealResidualFreeSlots S g i).not.mp hi
  have hi₀ : Fin.castAdd 0 i=i := Fin.ext rfl
  rw [hi₀]
  simp [idealSelectedFill,idealFlattenLabels,finiteProductFill,hn]


theorem idealRawPhase_selected {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (A B : Finset (G × Fin k)) (hAB : Disjoint A B)
    (Θ ζ : ℝ) (a : MarkedPhysicalMarking P (k+ell)) :
    idealRawPhase Θ ζ a=
      (giantTwoSidedPatternCopiedProduct (idealResidualFreeSlots (A ∪ B)) a:ℂ)^((ζ:ℂ)*Complex.I)*
        idealProductPhase ζ (Θ*(giantTwoSidedPatternCopiedProduct (idealResidualFreeSlots (A ∪ B)) a:ℝ))
          (idealSelectedProduct (idealResidualSelectedMarking A a))
          (idealSelectedProduct (idealResidualSelectedMarking B a)) := by
  change idealDilationPhase Θ ζ (giantTwoSidedPatternCopiedProduct (fun _ => (∅ : Finset (Fin k))) a)= _
  rw [idealResidual_copied_product P A B hAB]
  exact idealDilationPhase_selected Θ ζ _ _ _

end
end ArtinMatthews
