module

public import ArtinMatthews.IdealResidualFamily
public import ArtinMatthews.IdealGroupedSelected
public import Mathlib.Data.Fintype.EquivFin


set_option backward.privateInPublic true
@[expose] public section

/-! Selected source slots are regrouped by their original prime band.
Every slot and every repeated prime label is retained. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def idealSelectedFiberIndexEquiv {G : Type*} [DecidableEq G] {M : ℕ}
    (S : Finset (G × Fin M)) :
    (Σ g,↥(idealResidualFreeSlots S g)) ≃ ↥S where
  toFun v := ⟨(v.1,v.2.val),(mem_idealResidualFreeSlots S v.1 v.2.val).mp v.2.property⟩
  invFun v := ⟨v.val.1,⟨v.val.2,(mem_idealResidualFreeSlots S v.val.1 v.val.2).mpr v.property⟩⟩
  left_inv v := by cases v; rfl
  right_inv v := by cases v; rfl

def idealSelectedNumberedIndexEquiv {G : Type*} [DecidableEq G] {M : ℕ}
    (S : Finset (G × Fin M)) :
    (Σ g,Fin (idealResidualFreeSlots S g).card) ≃ ↥S :=
  (Equiv.sigmaCongrRight (fun g => (idealResidualFreeSlots S g).equivFin.symm)).trans
    (idealSelectedFiberIndexEquiv S)

def idealSelectedFinIndexEquiv {G : Type*} [DecidableEq G] {M : ℕ}
    (S : Finset (G × Fin M)) : ↥S ≃ (Σ g,Fin (idealResidualFreeSlots S g).card) :=
  (idealSelectedNumberedIndexEquiv S).symm

theorem idealSelectedNumberedIndexEquiv_group {G : Type*} [DecidableEq G] {M : ℕ}
    (S : Finset (G × Fin M)) (v : Σ g,Fin (idealResidualFreeSlots S g).card) :
    (idealSelectedNumberedIndexEquiv S v).val.1=v.1 := rfl

def idealSelectedGroupedEquiv {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {M : ℕ} (S : Finset (G × Fin M)) :
    IdealSelectedLabels (idealResidualBands P S) ≃
      IdealGroupedLabels P (fun g => (idealResidualFreeSlots S g).card) where
  toFun a g i := a (idealSelectedNumberedIndexEquiv S ⟨g,i⟩)
  invFun a v := a v.val.1 ((idealResidualFreeSlots S v.val.1).equivFin
    ⟨v.val.2,(mem_idealResidualFreeSlots S v.val.1 v.val.2).mpr v.property⟩)
  left_inv a := by
    funext v
    rcases v with ⟨⟨g,i⟩,hi⟩
    let w : ↥(idealResidualFreeSlots S g) :=
      ⟨i,(mem_idealResidualFreeSlots S g i).mpr hi⟩
    let label (z : ↥(idealResidualFreeSlots S g)) : ↥(P g) :=
      a ⟨(g,z.val),(mem_idealResidualFreeSlots S g z.val).mp z.property⟩
    change label ((idealResidualFreeSlots S g).equivFin.symm
      ((idealResidualFreeSlots S g).equivFin w))=label w
    exact congrArg label ((idealResidualFreeSlots S g).equivFin.symm_apply_apply w)
  right_inv a := by
    funext g i
    change a g ((idealResidualFreeSlots S g).equivFin
      ((idealResidualFreeSlots S g).equivFin.symm i))=a g i
    exact congrArg (a g) ((idealResidualFreeSlots S g).equivFin.apply_symm_apply i)

theorem idealSelectedGrouped_prod {G R : Type*} [Fintype G] [DecidableEq G] [CommMonoid R]
    (P : G → Finset ℕ) {M : ℕ} (S : Finset (G × Fin M))
    (F : ∀ g,↥(P g) → R) (a : IdealSelectedLabels (idealResidualBands P S)) :
    (∏ v : ↥S,F v.val.1 (a v))=
      ∏ g,∏ i : Fin (idealResidualFreeSlots S g).card,F g (idealSelectedGroupedEquiv P S a g i) := by
  change (∏ v : ↥S,F v.val.1 (a v))=
    ∏ g,∏ i : Fin (idealResidualFreeSlots S g).card,F g (a (idealSelectedNumberedIndexEquiv S ⟨g,i⟩))
  have h := Equiv.prod_comp (idealSelectedNumberedIndexEquiv S)
    (fun v : ↥S => F v.val.1 (a v))
  simpa only [Fintype.prod_sigma,idealSelectedNumberedIndexEquiv_group] using h.symm

theorem idealSelectedGrouped_mass {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {M : ℕ} (S : Finset (G × Fin M))
    (a : IdealSelectedLabels (idealResidualBands P S)) :
    idealSelectedMass (idealResidualBands P S) a=
      idealGroupedMass P (fun g => (idealResidualFreeSlots S g).card) (idealSelectedGroupedEquiv P S a) :=
  idealSelectedGrouped_prod P S (fun g => markedHarmonicAtom (P g)) a

theorem idealSelectedGrouped_product {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {M : ℕ} (S : Finset (G × Fin M))
    (a : IdealSelectedLabels (idealResidualBands P S)) :
    idealSelectedProduct a=idealGroupedProduct (idealSelectedGroupedEquiv P S a) :=
  idealSelectedGrouped_prod P S (fun _ p => p.val) a

theorem idealSelectedGrouped_energy {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {M : ℕ} (S : Finset (G × Fin M))
    (f : IdealSelectedLabels (idealResidualBands P S) → ℂ) :
    (∑ a,idealSelectedMass (idealResidualBands P S) a*‖f a‖^2)=
      ∑ b : IdealGroupedLabels P (fun g => (idealResidualFreeSlots S g).card),
        idealGroupedMass P (fun g => (idealResidualFreeSlots S g).card) b*
          ‖f ((idealSelectedGroupedEquiv P S).symm b)‖^2 := by
  rw [← (idealSelectedGroupedEquiv P S).symm.sum_comp]
  apply sum_congr rfl
  intro b _
  rw [idealSelectedGrouped_mass,Equiv.apply_symm_apply]

theorem idealSelectedGrouped_coefficient {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {M : ℕ} (S : Finset (G × Fin M))
    (f : IdealSelectedLabels (idealResidualBands P S) → ℂ) (n : ℕ) :
    (∑ a,if idealSelectedProduct a=n then (idealSelectedMass (idealResidualBands P S) a:ℂ)*f a else 0)=
      ∑ b : IdealGroupedLabels P (fun g => (idealResidualFreeSlots S g).card),
        if idealGroupedProduct b=n then
          (idealGroupedMass P (fun g => (idealResidualFreeSlots S g).card) b:ℂ)*
            f ((idealSelectedGroupedEquiv P S).symm b) else 0 := by
  rw [← (idealSelectedGroupedEquiv P S).symm.sum_comp]
  apply sum_congr rfl
  intro b _
  rw [idealSelectedGrouped_mass,idealSelectedGrouped_product,Equiv.apply_symm_apply]

def idealSelectedSigmaFinEquiv {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {M : ℕ} (S : Finset (G × Fin M)) :
    IdealSelectedLabels (idealResidualBands P S) ≃
      IdealSelectedLabels (fun v : Σ g,Fin (idealResidualFreeSlots S g).card => P v.1) :=
  (idealSelectedGroupedEquiv P S).trans
    (idealGroupedSelectedEquiv P (fun g => (idealResidualFreeSlots S g).card)).symm

theorem idealSelectedSigmaFin_mass {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {M : ℕ} (S : Finset (G × Fin M))
    (a : IdealSelectedLabels (idealResidualBands P S)) :
    idealSelectedMass (idealResidualBands P S) a=
      idealSelectedMass (fun v : Σ g,Fin (idealResidualFreeSlots S g).card => P v.1)
        (idealSelectedSigmaFinEquiv P S a) := by
  rw [idealGroupedSelected_mass,idealSelectedGrouped_mass]
  rfl

theorem idealSelectedSigmaFin_product {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {M : ℕ} (S : Finset (G × Fin M))
    (a : IdealSelectedLabels (idealResidualBands P S)) :
    idealSelectedProduct a=idealSelectedProduct (idealSelectedSigmaFinEquiv P S a) := by
  rw [idealGroupedSelected_product,idealSelectedGrouped_product]
  rfl

end
end ArtinMatthews
