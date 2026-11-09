module

public import ArtinMatthews.IdealSelectedFill
public import ArtinMatthews.IdealSelectedUnion


set_option backward.privateInPublic true
@[expose] public section

/-! Conditioning on the complementary labels leaves the two selected
sets with their original independent harmonic laws. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealSelectedFill_invariant {G : Type*} {P : G → Finset ℕ} {M : ℕ}
    (S : Finset (G × Fin M)) (f : MarkedPhysicalMarking P M → ℂ)
    (hf : ∀ a b,f (idealMix S a b)=f a) (a : MarkedPhysicalMarking P M)
    (x : IdealSelectedLabels (idealFullSelectedBands P S)) : f (idealSelectedFill S a x)=f a := by
  have he : idealMix S a (idealSelectedFill S a x)=idealSelectedFill S a x := by
    funext g i
    by_cases hi : (g,i)∈S
    · simp [idealMix,idealSelectedFill,idealFlattenLabels,finiteProductFill,hi]
      rfl
    · simp [idealMix,idealSelectedFill,idealFlattenLabels,finiteProductFill,hi]
  rw [← he]
  exact hf _ _

theorem idealSelectedFill_union_left {G : Type*} [DecidableEq G] {P : G → Finset ℕ} {M : ℕ}
    (S T : Finset (G × Fin M)) (hST : Disjoint S T) (a : MarkedPhysicalMarking P M)
    (x : IdealSelectedLabels (idealResidualBands P S))
    (y : IdealSelectedLabels (idealResidualBands P T)) :
    idealSelectedFill (S ∪ T) a ((idealSelectedUnionEquiv P S T hST).symm (x,y))=
      idealSelectedFill S (idealSelectedFill T a y) x := by
  funext g i
  by_cases hS : (g,i)∈S
  · have hU : (g,i)∈S ∪ T := mem_union_left T hS
    simp [idealSelectedFill,idealFlattenLabels,finiteProductFill,idealSelectedUnionEquiv,hS,hU]
    rfl
  · by_cases hT : (g,i)∈T
    · have hU : (g,i)∈S ∪ T := mem_union_right S hT
      simp [idealSelectedFill,idealFlattenLabels,finiteProductFill,idealSelectedUnionEquiv,hS,hT,hU]
      rfl
    · have hU : (g,i)∉S ∪ T := by simpa only [mem_union,not_or] using And.intro hS hT
      simp [idealSelectedFill,idealFlattenLabels,finiteProductFill,idealSelectedUnionEquiv,hS,hT,hU]

theorem idealSelectedFill_union_right {G : Type*} [DecidableEq G] {P : G → Finset ℕ} {M : ℕ}
    (S T : Finset (G × Fin M)) (hST : Disjoint S T) (a : MarkedPhysicalMarking P M)
    (x : IdealSelectedLabels (idealResidualBands P S))
    (y : IdealSelectedLabels (idealResidualBands P T)) :
    idealSelectedFill (S ∪ T) a ((idealSelectedUnionEquiv P S T hST).symm (x,y))=
      idealSelectedFill T (idealSelectedFill S a x) y := by
  rw [idealSelectedFill_union_left]
  funext g i
  by_cases hS : (g,i)∈S
  · have hT : (g,i)∉T := fun h => disjoint_left.mp hST hS h
    simp [idealSelectedFill,idealFlattenLabels,finiteProductFill,hS,hT]
    rfl
  · by_cases hT : (g,i)∈T
    · simp [idealSelectedFill,idealFlattenLabels,finiteProductFill,hS,hT]
      rfl
    · simp [idealSelectedFill,idealFlattenLabels,finiteProductFill,hS,hT]

theorem idealSelectedConditional_reindex {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {M : ℕ} (hV : ∀ g,0 < bandReciprocalMass (P g))
    (S T : Finset (G × Fin M)) (hST : Disjoint S T) (F : MarkedPhysicalMarking P M → ℂ) :
    idealLabelExpectation P M F=
      idealLabelExpectation P M (fun a =>
        ∑ x : IdealSelectedLabels (idealResidualBands P S),
          ∑ y : IdealSelectedLabels (idealResidualBands P T),
            (idealSelectedMass (idealResidualBands P S) x:ℂ)*
            (idealSelectedMass (idealResidualBands P T) y:ℂ)*
            F (idealSelectedFill (S ∪ T) a ((idealSelectedUnionEquiv P S T hST).symm (x,y)))) := by
  rw [← idealSelectedFill_full_expectation P hV (S ∪ T) F]
  apply congrArg (idealLabelExpectation P M)
  funext a
  exact idealSelectedUnion_expectation P S T hST (fun z => F (idealSelectedFill (S ∪ T) a z))

end
end ArtinMatthews
