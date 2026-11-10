module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite regrouping by a label, with no multiplicity loss when
the supplied value map is injective. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section

variable {ι M C : Type*} [Fintype ι] [DecidableEq M] [DecidableEq C]

def finiteFamilyImageAt (label : ι → M) (value : ι → C) (m : M) : Finset C :=
  (Finset.univ.filter (fun i => label i=m)).image value

theorem mem_finiteFamilyImageAt (label : ι → M) (value : ι → C) (m : M) (c : C) :
    c ∈ finiteFamilyImageAt label value m ↔ ∃ i, label i=m ∧ value i=c := by
  simp only [finiteFamilyImageAt,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]

theorem finiteFamilyImageAt_filter_card (label : ι → M) (value : ι → C)
    (hinj : Function.Injective value) (m : M) (P : C → Prop) :
    ((finiteFamilyImageAt label value m).filter P).card=
      (Finset.univ.filter (fun i => label i=m ∧ P (value i))).card := by
  rw [finiteFamilyImageAt,Finset.filter_image,Finset.card_image_of_injective _ hinj,
    Finset.filter_filter]

theorem finiteFamilyImageAt_filter_card_sum (label : ι → M) (value : ι → C)
    (hinj : Function.Injective value) (P : C → Prop) :
    (∑ m ∈ Finset.univ.image label, ((finiteFamilyImageAt label value m).filter P).card)=
      ((Finset.univ.image value).filter P).card := by
  calc
    _ = ∑ m ∈ Finset.univ.image label,
        (Finset.univ.filter (fun i => label i=m ∧ P (value i))).card := by
      apply Finset.sum_congr rfl
      intro m _
      exact finiteFamilyImageAt_filter_card label value hinj m P
    _ = (Finset.univ.filter (fun i => P (value i))).card := by
      have h := Finset.card_eq_sum_card_fiberwise (f := label)
        (s := Finset.univ.filter (fun i => P (value i))) (t := Finset.univ.image label)
        (fun i _ => Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
      simpa only [Finset.filter_filter,and_comm] using h.symm
    _ = _ := by
      rw [Finset.filter_image,Finset.card_image_of_injective _ hinj]

end
end ArtinMatthews
