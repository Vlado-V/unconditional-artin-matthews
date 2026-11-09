module

public import ArtinMatthews.IdealResidualFamily
public import ArtinMatthews.IdealPatternFreeCoordinates
public import ArtinMatthews.IdealProductSwap


set_option backward.privateInPublic true
@[expose] public section

/-! Swapping the first freed block brings the actual comparison row
onto the same full label vector as the raw pairing. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealResidualSwap_copied {G : Type*} [Fintype G] [DecidableEq G]
    {P : G → Finset ℕ} {k ell : ℕ} (A B : Finset (G × Fin k))
    (a b : MarkedPhysicalMarking P (k+ell)) :
    giantTwoSidedPatternCopiedProduct (idealResidualFreeSlots (A ∪ B))
      (idealMix (idealPatternFreeCoordinates (idealResidualFreeSlots A)) a b)=
      giantTwoSidedPatternCopiedProduct (idealResidualFreeSlots (A ∪ B)) a := by
  apply giantTwoSidedPatternCopiedProduct_eq
  intro g i hi
  have hA : (g,i)∉A := by
    intro h
    exact hi ((mem_idealResidualFreeSlots (A ∪ B) g i).mpr (mem_union_left B h))
  simp only [idealMix,idealPatternFreeCoordinates_first,mem_idealResidualFreeSlots,hA,ite_false]

theorem idealResidualSwap_source_selected {G : Type*} [Fintype G] [DecidableEq G]
    {P : G → Finset ℕ} {k ell : ℕ} (A B : Finset (G × Fin k)) (hAB : Disjoint A B)
    (a b : MarkedPhysicalMarking P (k+ell)) :
    idealResidualSelectedMarking B
      (idealMix (idealPatternFreeCoordinates (idealResidualFreeSlots A)) a b)=
      idealResidualSelectedMarking B a := by
  funext v
  have hA : v.val∉A := fun h => disjoint_left.mp hAB h v.property
  simp only [idealResidualSelectedMarking,idealMix,idealPatternFreeCoordinates_first,
    mem_idealResidualFreeSlots,hA,ite_false]
  rfl

theorem idealResidualSwap_target_selected {G : Type*} [Fintype G] [DecidableEq G]
    {P : G → Finset ℕ} {k ell : ℕ} (A B : Finset (G × Fin k))
    (a b : MarkedPhysicalMarking P (k+ell)) :
    idealResidualSelectedMarking A
      (idealMix (idealPatternFreeCoordinates (idealResidualFreeSlots (A ∪ B)))
        (idealMix (idealPatternFreeCoordinates (idealResidualFreeSlots A)) a b)
        (idealMix (idealPatternFreeCoordinates (idealResidualFreeSlots A)) b a))=
      idealResidualSelectedMarking A a := by
  funext v
  have hAB : v.val∈A ∪ B := mem_union_left B v.property
  simp only [idealResidualSelectedMarking,idealMix,idealPatternFreeCoordinates_first,
    mem_idealResidualFreeSlots,hAB,v.property,ite_true]
  rfl

theorem idealResidualSwap_target_outside {G : Type*} [Fintype G] [DecidableEq G]
    {P : G → Finset ℕ} {k ell : ℕ} (A B : Finset (G × Fin k))
    (a b : MarkedPhysicalMarking P (k+ell)) (g : G) (i : Fin (k+ell))
    (hi : (g,i)∉idealPatternFreeCoordinates (idealResidualFreeSlots B)) :
    idealMix (idealPatternFreeCoordinates (idealResidualFreeSlots (A ∪ B)))
      (idealMix (idealPatternFreeCoordinates (idealResidualFreeSlots A)) a b)
      (idealMix (idealPatternFreeCoordinates (idealResidualFreeSlots A)) b a) g i=a g i := by
  induction i using Fin.addCases with
  | left i =>
    have hB : (g,i)∉B := by
      simpa only [idealPatternFreeCoordinates_first,mem_idealResidualFreeSlots] using hi
    by_cases hA : (g,i)∈A <;>
      simp only [idealMix,idealPatternFreeCoordinates_first,mem_idealResidualFreeSlots,
        mem_union,hA,hB,or_false,ite_true,ite_false]
  | right i => exact (hi (idealPatternFreeCoordinates_tail _ g i)).elim

theorem idealResidualSwap_target_function {G : Type*} [Fintype G] [DecidableEq G]
    {P : G → Finset ℕ} {k ell : ℕ} (A B : Finset (G × Fin k))
    (f : MarkedPhysicalMarking P (k+ell) → ℂ)
    (hf : ∀ a b,f (idealMix (idealPatternFreeCoordinates (idealResidualFreeSlots B)) a b)=f a)
    (a b : MarkedPhysicalMarking P (k+ell)) :
    f (idealMix (idealPatternFreeCoordinates (idealResidualFreeSlots (A ∪ B)))
      (idealMix (idealPatternFreeCoordinates (idealResidualFreeSlots A)) a b)
      (idealMix (idealPatternFreeCoordinates (idealResidualFreeSlots A)) b a))=f a := by
  have he := idealMix_eq_self_of_eq_outside
    (idealPatternFreeCoordinates (idealResidualFreeSlots B)) a
    (idealMix (idealPatternFreeCoordinates (idealResidualFreeSlots (A ∪ B)))
      (idealMix (idealPatternFreeCoordinates (idealResidualFreeSlots A)) a b)
      (idealMix (idealPatternFreeCoordinates (idealResidualFreeSlots A)) b a))
    (idealResidualSwap_target_outside A B a b)
  rw [← he]
  exact hf _ _

theorem idealResidualSwap_coefficient {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (A B : Finset (G × Fin k)) (hAB : Disjoint A B)
    (Q : ℕ) (h ξ : ℝ) (a b : MarkedPhysicalMarking P (k+ell))
    (aux : GiantTwoSidedPatternAuxiliary P (idealResidualFreeSlots (A ∪ B))) :
    idealResidualCoefficient P Q h ξ (some (A,B))
      (idealMix (idealPatternFreeCoordinates (idealResidualFreeSlots A)) a b)
      (idealMix (idealPatternFreeCoordinates (idealResidualFreeSlots (A ∪ B)))
        (idealMix (idealPatternFreeCoordinates (idealResidualFreeSlots A)) a b)
        (idealMix (idealPatternFreeCoordinates (idealResidualFreeSlots A)) b a)) aux=
      idealResidualCoefficient P Q h ξ (some (A,B)) a a aux := by
  dsimp only [idealResidualCoefficient,idealResidualCopied]
  rw [idealResidualSwap_source_selected A B hAB,idealResidualSwap_target_selected]

end
end ArtinMatthews
