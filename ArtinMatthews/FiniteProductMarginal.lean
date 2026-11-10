module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt


set_option backward.privateInPublic true
@[expose] public section

/-! Exact marginals and copied-coordinate sums for normalized finite
product laws. No support restriction is imposed on the test function. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def finiteProductMarginalMass {I R : Type*} [Fintype I] [CommSemiring R]
    {A : I → Type*} (w : ∀ i,A i → R) (x : ∀ i,A i) : R :=
  ∏ i,w i (x i)

def finiteProductRestriction {I : Type*} {A : I → Type*} (S : Finset I)
    (x : ∀ i,A i) : ∀ i : {i // i∈S},A i := fun i => x i

theorem finiteProductMarginalMass_sum {I R : Type*} [Fintype I] [DecidableEq I]
    [CommSemiring R] {A : I → Type*} [∀ i,Fintype (A i)]
    (w : ∀ i,A i → R) (hw : ∀ i,∑ a,w i a=1) :
    (∑ x : ∀ i,A i,finiteProductMarginalMass w x)=1 := by
  unfold finiteProductMarginalMass
  rw [← Fintype.prod_sum]
  simp only [hw,prod_const_one]

theorem finiteProductMarginal {I R : Type*} [Fintype I] [DecidableEq I]
    [CommSemiring R] {A : I → Type*} [∀ i,Fintype (A i)]
    (w : ∀ i,A i → R) (hw : ∀ i,∑ a,w i a=1) (S : Finset I)
    (F : (∀ i : {i // i∈S},A i) → R) :
    (∑ x : ∀ i,A i,finiteProductMarginalMass w x*F (finiteProductRestriction S x))=
      ∑ y : ∀ i : {i // i∈S},A i,
        finiteProductMarginalMass (fun i : {i // i∈S} => w i) y*F y := by
  let e := Equiv.piEquivPiSubtypeProd (fun i => i∈S) A
  have hm (z : (∀ i : {i // i∈S},A i) × (∀ i : {i // i∉S},A i)) :
      finiteProductMarginalMass w (e.symm z)=
        finiteProductMarginalMass (fun i : {i // i∈S} => w i) z.1*
        finiteProductMarginalMass (fun i : {i // i∉S} => w i) z.2 := by
    unfold finiteProductMarginalMass
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun i => i∈S)]
    congr 1
    · refine Finset.prod_congr ?_ ?_
      · ext i
        simp
      · intro i _
        simp [e,Equiv.piEquivPiSubtypeProd,i.property]
    · refine Finset.prod_congr ?_ ?_
      · ext i
        simp
      · intro i _
        simp [e,Equiv.piEquivPiSubtypeProd,i.property]
  have hr (z : (∀ i : {i // i∈S},A i) × (∀ i : {i // i∉S},A i)) :
      finiteProductRestriction S (e.symm z)=z.1 := by
    funext i
    simp [finiteProductRestriction,e,Equiv.piEquivPiSubtypeProd,i.property]
  rw [← e.symm.sum_comp]
  simp only [hm,hr,Fintype.sum_prod_type]
  apply sum_congr rfl
  intro y _
  calc
    _ = (finiteProductMarginalMass (fun i : {i // i∈S} => w i) y*F y)*
        ∑ z : ∀ i : {i // i∉S},A i,finiteProductMarginalMass (fun i : {i // i∉S} => w i) z := by
      rw [mul_sum]
      apply sum_congr rfl
      intro z _
      ring
    _ = _ := by rw [finiteProductMarginalMass_sum (I:={i // i∉S}) (A:=fun i => A i)
        (fun i => w i) (fun i => hw i),mul_one]

def finiteProductFill {I : Type*} {A : I → Type*} (S : Finset I)
    (a : ∀ i,A i) (y : ∀ i : {i // i∈S},A i) : ∀ i,A i :=
  fun i => if hi : i∈S then y ⟨i,hi⟩ else a i

theorem finiteProductFixedComplement_sum {I R : Type*} [Fintype I] [DecidableEq I]
    [CommSemiring R] {A : I → Type*} [∀ i,Fintype (A i)]
    (w : ∀ i,A i → R) (S : Finset I) (a : ∀ i,A i) (F : (∀ i,A i) → R) :
    (∑ x : ∀ i,A i,
      if ∀ i,i∉S → x i=a i then
        finiteProductMarginalMass (fun i : {i // i∈S} => w i) (finiteProductRestriction S x)*F x
      else 0)=
      ∑ y : ∀ i : {i // i∈S},A i,
        finiteProductMarginalMass (fun i : {i // i∈S} => w i) y*F (finiteProductFill S a y) := by
  let e := Equiv.piEquivPiSubtypeProd (fun i => i∈S) A
  let z₀ : ∀ i : {i // i∉S},A i := fun i => a i
  have hr (y : ∀ i : {i // i∈S},A i) (z : ∀ i : {i // i∉S},A i) :
      finiteProductRestriction S (e.symm (y,z))=y := by
    funext i
    simp [finiteProductRestriction,e,Equiv.piEquivPiSubtypeProd,i.property]
  have hc (y : ∀ i : {i // i∈S},A i) (z : ∀ i : {i // i∉S},A i) :
      (∀ i,i∉S → e.symm (y,z) i=a i) ↔ z=z₀ := by
    constructor
    · intro h
      funext i
      have hi := h i i.property
      simpa only [e,Equiv.piEquivPiSubtypeProd,Equiv.coe_fn_symm_mk,
        dite_eq_right i.property,z₀] using hi
    · rintro rfl i hi
      simp [e,Equiv.piEquivPiSubtypeProd,hi,z₀]
  have hf (y : ∀ i : {i // i∈S},A i) : e.symm (y,z₀)=finiteProductFill S a y := by
    funext i
    by_cases hi : i∈S <;> simp [e,Equiv.piEquivPiSubtypeProd,finiteProductFill,hi,z₀]
  rw [← e.symm.sum_comp]
  simp only [Fintype.sum_prod_type,hr,hc]
  apply sum_congr rfl
  intro y _
  rw [sum_eq_single z₀]
  · rw [ite_eq_left rfl,hf]
  · intro z _ hz
    exact ite_eq_right hz
  · intro h
    exact (h (mem_univ z₀)).elim

end
end ArtinMatthews
