module

public import ArtinMatthews.IdealProductRestriction
public import ArtinMatthews.IdealLabelOperator
public import Mathlib.Algebra.BigOperators.Fin


set_option backward.privateInPublic true
@[expose] public section

/-! The original copied/free pattern has an exact full-coordinate
description. Its fresh mass is the marginal law on those coordinates. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def IdealPatternFreeCoordinate {J : Type*} {k ell : ℕ}
    (C : J → Finset (Fin k)) (v : J × Fin (k+ell)) : Prop :=
  Fin.addCases (fun i => i∈C v.1) (fun _ => True) v.2

def idealPatternFreeCoordinates {J : Type*} [Fintype J] [DecidableEq J] {k ell : ℕ}
    (C : J → Finset (Fin k)) : Finset (J × Fin (k+ell)) :=
  univ.filter (IdealPatternFreeCoordinate C)

theorem idealPatternFreeCoordinates_first {J : Type*} [Fintype J] [DecidableEq J] {k ell : ℕ}
    (C : J → Finset (Fin k)) (j : J) (i : Fin k) :
    (j,Fin.castAdd ell i)∈idealPatternFreeCoordinates C ↔ i∈C j := by
  simp [idealPatternFreeCoordinates,IdealPatternFreeCoordinate]

theorem idealPatternFreeCoordinates_tail {J : Type*} [Fintype J] [DecidableEq J] {k ell : ℕ}
    (C : J → Finset (Fin k)) (j : J) (i : Fin ell) :
    (j,Fin.natAdd k i)∈idealPatternFreeCoordinates C := by
  simp [idealPatternFreeCoordinates,IdealPatternFreeCoordinate]

theorem idealCopied_iff_freeComplement {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k ell : ℕ} (C : J → Finset (Fin k))
    (a b : MarkedPhysicalMarking P (k+ell)) :
    IdealCopied C a b ↔ ∀ v : J × Fin (k+ell),v∉idealPatternFreeCoordinates C →
      idealFlattenLabels b v=idealFlattenLabels a v := by
  constructor
  · intro h v
    rcases v with ⟨j,i⟩
    refine Fin.addCases ?_ ?_ i
    · intro i hi
      exact h j i ((idealPatternFreeCoordinates_first C j i).not.mp hi)
    · intro i hi
      exact (hi (idealPatternFreeCoordinates_tail C j i)).elim
  · intro h j i hi
    exact h (j,Fin.castAdd ell i) ((idealPatternFreeCoordinates_first C j i).not.mpr hi)

theorem finiteProductRestrictedMass_eq_ite {I R : Type*} [Fintype I] [DecidableEq I]
    [CommSemiring R] {A : I → Type*} (w : ∀ i,A i → R) (S : Finset I) (x : ∀ i,A i) :
    finiteProductMarginalMass (fun i : ↥S => w i) (finiteProductRestriction S x)=
      ∏ i : I,if i∈S then w i (x i) else 1 := by
  unfold finiteProductMarginalMass finiteProductRestriction
  have hp : (∏ i : ↥S,w i.val (x i.val))=∏ i∈S,w i (x i) :=
    prod_coe_sort S (fun i => w i (x i))
  rw [hp]
  symm
  simpa only [univ_inter] using prod_ite_mem univ S (fun i => w i (x i))

theorem idealPatternFreshMass_eq_restricted {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k ell : ℕ} (law : ∀ j,↥(P j) → ℝ)
    (C : J → Finset (Fin k)) (b : MarkedPhysicalMarking P (k+ell)) :
    finiteProductMarginalMass (fun v : ↥(idealPatternFreeCoordinates C) => law v.val.1)
      (finiteProductRestriction (idealPatternFreeCoordinates C) (idealFlattenLabels b))=
      idealFreshTargetMass law C b := by
  rw [finiteProductRestrictedMass_eq_ite (fun v : J × Fin (k+ell) => law v.1)]
  rw [Fintype.prod_prod_type]
  unfold idealFreshTargetMass
  apply prod_congr rfl
  intro j _
  rw [Fin.prod_univ_add,Fintype.prod_sum_type]
  simp only [idealPatternFreeCoordinates_first,idealPatternFreeCoordinates_tail,ite_true,
    giantTwoSidedPatternFreeSlot,Sum.elim_inl,Sum.elim_inr,idealFlattenLabels,Equiv.coe_fn_mk]
  congr 1
  have hp : (∏ i : ↥(C j),law j (b j (Fin.castAdd ell i.val)))=
      ∏ i∈C j,law j (b j (Fin.castAdd ell i)) :=
    prod_coe_sort (C j) (fun i => law j (b j (Fin.castAdd ell i)))
  rw [hp]
  simpa only [univ_inter] using prod_ite_mem univ (C j)
    (fun i => law j (b j (Fin.castAdd ell i)))

end
end ArtinMatthews
