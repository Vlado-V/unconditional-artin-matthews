module

public import ArtinMatthews.IdealSelectedFill
public import ArtinMatthews.IdealResidualFamily
public import Mathlib.Algebra.BigOperators.Fin


set_option backward.privateInPublic true
@[expose] public section

/-! The first and tail slots have their exact original independent
harmonic laws, including arbitrary full-tuple tests. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def idealLabelHead {G : Type*} {P : G → Finset ℕ} {k ell : ℕ}
    (a : MarkedPhysicalMarking P (k+ell)) : MarkedPhysicalMarking P k :=
  fun g i => a g (Fin.castAdd ell i)

def idealLabelTail {G : Type*} {P : G → Finset ℕ} {k ell : ℕ}
    (a : MarkedPhysicalMarking P (k+ell)) : MarkedPhysicalMarking P ell :=
  fun g i => a g (Fin.natAdd k i)

def idealLabelAppend {G : Type*} {P : G → Finset ℕ} {k ell : ℕ}
    (a : MarkedPhysicalMarking P k) (b : MarkedPhysicalMarking P ell) :
    MarkedPhysicalMarking P (k+ell) := fun g => Fin.addCases (a g) (b g)

def idealHeadTailEquiv {G : Type*} {P : G → Finset ℕ} {k ell : ℕ} :
    MarkedPhysicalMarking P (k+ell) ≃ MarkedPhysicalMarking P k × MarkedPhysicalMarking P ell where
  toFun a := (idealLabelHead a,idealLabelTail a)
  invFun a := idealLabelAppend a.1 a.2
  left_inv a := by
    funext g i
    induction i using Fin.addCases <;> simp [idealLabelAppend,idealLabelHead,idealLabelTail]
  right_inv a := by
    apply Prod.ext <;> funext g i <;> simp [idealLabelAppend,idealLabelHead,idealLabelTail]

theorem idealHeadTail_mass {G : Type*} [Fintype G] (P : G → Finset ℕ) {k ell : ℕ}
    (a : MarkedPhysicalMarking P (k+ell)) :
    idealLabelMass P (k+ell) a=idealLabelMass P k (idealLabelHead a)*idealLabelMass P ell (idealLabelTail a) := by
  unfold idealLabelMass
  rw [← prod_mul_distrib]
  apply prod_congr rfl
  intro g _
  rw [Fin.prod_univ_add]
  rfl

theorem idealHeadTail_expectation {G A : Type*} [Fintype G] [DecidableEq G]
    [CommRing A] [Algebra ℝ A] (P : G → Finset ℕ) {k ell : ℕ}
    (F : MarkedPhysicalMarking P (k+ell) → A) :
    idealLabelExpectation P (k+ell) F=
      idealLabelExpectation P k (fun a => idealLabelExpectation P ell (fun b => F (idealLabelAppend a b))) := by
  unfold idealLabelExpectation
  rw [← (idealHeadTailEquiv (P:=P) (k:=k) (ell:=ell)).symm.sum_comp,Fintype.sum_prod_type]
  apply sum_congr rfl
  intro a _
  rw [mul_sum]
  apply sum_congr rfl
  intro b _
  rw [idealHeadTail_mass,map_mul]
  have hh : idealLabelHead (idealLabelAppend a b)=a := by
    funext g i
    simp [idealLabelHead,idealLabelAppend]
  have ht : idealLabelTail (idealLabelAppend a b)=b := by
    funext g i
    simp [idealLabelTail,idealLabelAppend]
  change (algebraMap ℝ A) (idealLabelMass P k (idealLabelHead (idealLabelAppend a b)))*
    (algebraMap ℝ A) (idealLabelMass P ell (idealLabelTail (idealLabelAppend a b)))*F (idealLabelAppend a b)=_
  rw [hh,ht]
  ring

theorem idealResidualSelected_marginal {G A : Type*} [Fintype G] [DecidableEq G]
    [CommRing A] [Algebra ℝ A] (P : G → Finset ℕ) {k ell : ℕ}
    (hV : ∀ g,0 < bandReciprocalMass (P g)) (S : Finset (G × Fin k))
    (F : IdealSelectedLabels (idealResidualBands P S) → A) :
    idealLabelExpectation P (k+ell) (fun a => F (idealResidualSelectedMarking S a))=
      ∑ x : IdealSelectedLabels (idealResidualBands P S),
        algebraMap ℝ A (idealSelectedMass (idealResidualBands P S) x)*F x := by
  rw [idealHeadTail_expectation]
  have hi (a : MarkedPhysicalMarking P k) :
      idealLabelExpectation P ell (fun b => F (idealResidualSelectedMarking S (idealLabelAppend a b)))=
        F (idealFullSelectedLabels S a) := by
    have he (b : MarkedPhysicalMarking P ell) :
        idealResidualSelectedMarking S (idealLabelAppend a b)=idealFullSelectedLabels S a := by
      funext v
      simp [idealResidualSelectedMarking,idealFullSelectedLabels,idealLabelAppend]
      rfl
    have ht : (fun b : MarkedPhysicalMarking P ell =>
        F (idealResidualSelectedMarking S (idealLabelAppend a b)))=
        fun _ : MarkedPhysicalMarking P ell => F (idealFullSelectedLabels S a) :=
      funext (fun b => congrArg F (he b))
    rw [ht]
    unfold idealLabelExpectation
    rw [← sum_mul,← map_sum,idealLabelMass_sum P ell hV,map_one,one_mul]
  simp_rw [hi]
  exact idealFullSelected_marginal_scalar P hV S F

end
end ArtinMatthews
