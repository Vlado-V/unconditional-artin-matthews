module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! Exact inclusion-exclusion on the finite support of a product mode. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealProbe_disjoint_powerset {ι : Type*} [DecidableEq ι]
    (P U : Finset ι) :
    P.powerset.filter (fun S => Disjoint U S)=(P \ U).powerset := by
  ext S
  simp only [mem_filter,mem_powerset]
  constructor
  · rintro ⟨hSP,hUS⟩ x hx
    exact mem_sdiff.mpr ⟨hSP hx,fun hU => disjoint_left.mp hUS hU hx⟩
  · intro hS
    refine ⟨fun x hx => (mem_sdiff.mp (hS hx)).1,?_⟩
    exact disjoint_left.mpr fun x hU hSx => (mem_sdiff.mp (hS hSx)).2 hU

theorem idealProbe_alternating_sum {ι : Type*} [DecidableEq ι] (P : Finset ι) :
    (∑ S∈P.powerset,(-1:ℂ)^S.card)=if P=∅ then 1 else 0 := by
  have h := congrArg (fun z : ℤ => (z:ℂ)) (sum_powerset_neg_one_pow_card (x:=P))
  push_cast at h
  exact h

theorem idealProbe_alternating_mask {ι : Type*} [DecidableEq ι]
    (P T U : Finset ι) (z : ℂ) :
    (∑ S∈P.powerset,(-1:ℂ)^S.card*(if Disjoint U (T ∪ S) then z else 0))=
      if P ⊆ U ∧ Disjoint U T then z else 0 := by
  by_cases hT : Disjoint U T
  · have he (S : Finset ι) :
        (-1:ℂ)^S.card*(if Disjoint U (T ∪ S) then z else 0)=
          if Disjoint U S then (-1:ℂ)^S.card*z else 0 := by
      simp only [disjoint_union_right,hT,true_and]
      split_ifs <;> simp
    simp_rw [he]
    rw [← sum_filter,idealProbe_disjoint_powerset,← sum_mul,idealProbe_alternating_sum]
    simp only [sdiff_eq_empty_iff_subset,hT,and_true]
    split_ifs <;> simp
  · have he (S : Finset ι) : ¬Disjoint U (T ∪ S) := by
      simpa only [disjoint_union_right,not_and] using fun (h : Disjoint U T) => (hT h).elim
    simp only [he,ite_false,mul_zero,sum_const_zero,hT,and_false]

end
end ArtinMatthews
