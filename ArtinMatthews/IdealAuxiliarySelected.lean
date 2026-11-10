module

public import ArtinMatthews.IdealSelectedFibers
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

/-! The literal auxiliary tuple for a freed pattern is exactly the
selected-slot product carrier, with its original harmonic law. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def idealAuxiliarySelectedEquiv {G : Type*} [DecidableEq G]
    (P : G → Finset ℕ) {k : ℕ} (S : Finset (G × Fin k)) :
    GiantTwoSidedPatternAuxiliary P (idealResidualFreeSlots S) ≃
      IdealSelectedLabels (idealResidualBands P S) where
  toFun aux v := aux v.val.1 ⟨v.val.2,(mem_idealResidualFreeSlots S v.val.1 v.val.2).mpr v.property⟩
  invFun a g i := a ⟨(g,i.val),(mem_idealResidualFreeSlots S g i.val).mp i.property⟩
  left_inv aux := by funext g i; rfl
  right_inv a := by funext v; rcases v with ⟨⟨g,i⟩,hi⟩; rfl

theorem idealAuxiliarySelected_prod {G R : Type*} [Fintype G] [DecidableEq G] [CommMonoid R]
    (P : G → Finset ℕ) {k : ℕ} (S : Finset (G × Fin k))
    (F : ∀ g,↥(P g) → R) (aux : GiantTwoSidedPatternAuxiliary P (idealResidualFreeSlots S)) :
    (∏ g,∏ i : ↥(idealResidualFreeSlots S g),F g (aux g i))=
      ∏ v : ↥S,F v.val.1 (idealAuxiliarySelectedEquiv P S aux v) := by
  change (∏ g,∏ i : ↥(idealResidualFreeSlots S g),F g (aux g i))=
    ∏ v : ↥S,F v.val.1 (aux v.val.1
      ⟨v.val.2,(mem_idealResidualFreeSlots S v.val.1 v.val.2).mpr v.property⟩)
  have he := Equiv.prod_comp (idealSelectedFiberIndexEquiv S)
    (fun v : ↥S => F v.val.1 (aux v.val.1
      ⟨v.val.2,(mem_idealResidualFreeSlots S v.val.1 v.val.2).mpr v.property⟩))
  rw [Fintype.prod_sigma] at he
  simpa only [idealSelectedFiberIndexEquiv,Equiv.coe_fn_mk] using he

theorem idealAuxiliarySelected_mass {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k : ℕ} (S : Finset (G × Fin k))
    (aux : GiantTwoSidedPatternAuxiliary P (idealResidualFreeSlots S)) :
    giantTwoSidedPatternAuxiliaryMass aux=
      idealSelectedMass (idealResidualBands P S) (idealAuxiliarySelectedEquiv P S aux) :=
  idealAuxiliarySelected_prod P S (fun g => markedHarmonicAtom (P g)) aux

theorem idealAuxiliarySelected_product {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k : ℕ} (S : Finset (G × Fin k))
    (aux : GiantTwoSidedPatternAuxiliary P (idealResidualFreeSlots S)) :
    giantTwoSidedPatternAuxiliaryProduct aux=idealSelectedProduct (idealAuxiliarySelectedEquiv P S aux) :=
  idealAuxiliarySelected_prod P S (fun _ p => p.val) aux

theorem idealAuxiliarySelected_expectation {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k : ℕ} (S : Finset (G × Fin k))
    (F : GiantTwoSidedPatternAuxiliary P (idealResidualFreeSlots S) → ℂ) :
    (∑ aux,(giantTwoSidedPatternAuxiliaryMass aux:ℂ)*F aux)=
      ∑ a : IdealSelectedLabels (idealResidualBands P S),
        (idealSelectedMass (idealResidualBands P S) a:ℂ)*F ((idealAuxiliarySelectedEquiv P S).symm a) := by
  rw [← (idealAuxiliarySelectedEquiv P S).symm.sum_comp]
  apply sum_congr rfl
  intro a _
  rw [idealAuxiliarySelected_mass,Equiv.apply_symm_apply]

end
end ArtinMatthews
