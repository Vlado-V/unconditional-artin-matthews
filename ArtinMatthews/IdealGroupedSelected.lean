module

public import ArtinMatthews.IdealGroupedAtom


set_option backward.privateInPublic true
@[expose] public section

/-! Exact regrouping between selected slots and their per-band arrays. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {G : Type*} [Fintype G] [DecidableEq G]

def idealGroupedSelectedEquiv (P : G → Finset ℕ) (k : G → ℕ) :
    IdealSelectedLabels (fun z : Σ g, Fin (k g) => P z.1) ≃ IdealGroupedLabels P k where
  toFun a g i := a ⟨g, i⟩
  invFun a z := a z.1 z.2
  left_inv _ := rfl
  right_inv _ := rfl

omit [DecidableEq G] in
theorem idealGroupedSelected_mass (P : G → Finset ℕ) (k : G → ℕ)
    (a : IdealSelectedLabels (fun z : Σ g, Fin (k g) => P z.1)) :
    idealSelectedMass (fun z : Σ g, Fin (k g) => P z.1) a =
      idealGroupedMass P k (idealGroupedSelectedEquiv P k a) := by
  simp only [idealSelectedMass, idealGroupedMass, Fintype.prod_sigma]
  rfl

omit [DecidableEq G] in
theorem idealGroupedSelected_product (P : G → Finset ℕ) (k : G → ℕ)
    (a : IdealSelectedLabels (fun z : Σ g, Fin (k g) => P z.1)) :
    idealSelectedProduct a = idealGroupedProduct (idealGroupedSelectedEquiv P k a) := by
  simp only [idealSelectedProduct, idealGroupedProduct, idealGroupProduct, Fintype.prod_sigma]
  rfl

theorem idealGroupedSelected_energy (P : G → Finset ℕ) (k : G → ℕ)
    (f : IdealSelectedLabels (fun z : Σ g, Fin (k g) => P z.1) → ℂ) :
    (∑ a, idealSelectedMass (fun z : Σ g, Fin (k g) => P z.1) a * ‖f a‖^2) =
      ∑ b : IdealGroupedLabels P k, idealGroupedMass P k b *
        ‖f ((idealGroupedSelectedEquiv P k).symm b)‖^2 := by
  rw [← (idealGroupedSelectedEquiv P k).symm.sum_comp
    (fun a => idealSelectedMass (fun z : Σ g, Fin (k g) => P z.1) a * ‖f a‖^2)]
  apply sum_congr rfl
  intro b _
  rw [idealGroupedSelected_mass, Equiv.apply_symm_apply]

theorem idealGroupedSelected_coefficient (P : G → Finset ℕ) (k : G → ℕ)
    (f : IdealSelectedLabels (fun z : Σ g, Fin (k g) => P z.1) → ℂ) (n : ℕ) :
    (∑ a, if idealSelectedProduct a = n then
      (idealSelectedMass (fun z : Σ g, Fin (k g) => P z.1) a : ℂ) * f a else 0) =
      ∑ b : IdealGroupedLabels P k, if idealGroupedProduct b = n then
        (idealGroupedMass P k b : ℂ) * f ((idealGroupedSelectedEquiv P k).symm b) else 0 := by
  rw [← (idealGroupedSelectedEquiv P k).symm.sum_comp
    (fun a => if idealSelectedProduct a = n then
      (idealSelectedMass (fun z : Σ g, Fin (k g) => P z.1) a : ℂ) * f a else 0)]
  apply sum_congr rfl
  intro b _
  rw [idealGroupedSelected_product, idealGroupedSelected_mass, Equiv.apply_symm_apply]

end
end ArtinMatthews
