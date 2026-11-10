module

public import ArtinMatthews.IdealGroupedAtom
public import ArtinMatthews.IdealSelectedLabels
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
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
public import Mathlib.Topology.Sheaves.Init


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
