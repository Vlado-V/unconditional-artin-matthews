module

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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! Exact one-coordinate disintegration of the selected harmonic law. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev idealSelectedRest (P : I → Finset ℕ) (i : I) : {j : I // j ≠ i} → Finset ℕ :=
  fun j => P j.val

def idealSelectedJoin (P : I → Finset ℕ) (i : I)
    (p : ↥(P i)) (b : IdealSelectedLabels (idealSelectedRest P i)) : IdealSelectedLabels P :=
  (Equiv.piSplitAt i (fun j => ↥(P j))).symm (p, b)

omit [Fintype I] in
theorem idealSelectedJoin_at (P : I → Finset ℕ) (i : I)
    (p : ↥(P i)) (b : IdealSelectedLabels (idealSelectedRest P i)) :
    idealSelectedJoin P i p b i = p := by
  simp [idealSelectedJoin, Equiv.piSplitAt]

omit [Fintype I] in
theorem idealSelectedJoin_rest (P : I → Finset ℕ) (i : I)
    (p : ↥(P i)) (b : IdealSelectedLabels (idealSelectedRest P i)) :
    (fun j : {j : I // j ≠ i} => idealSelectedJoin P i p b j.val) = b := by
  funext j
  simp only [idealSelectedJoin, Equiv.piSplitAt_symm_apply, dite_eq_right j.property]

theorem idealSelectedMass_join (P : I → Finset ℕ) (i : I)
    (p : ↥(P i)) (b : IdealSelectedLabels (idealSelectedRest P i)) :
    idealSelectedMass P (idealSelectedJoin P i p b) =
      markedHarmonicAtom (P i) p * idealSelectedMass (idealSelectedRest P i) b := by
  unfold idealSelectedMass
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ i, idealSelectedJoin_at]
  apply congrArg (fun z : ℝ => markedHarmonicAtom (P i) p * z)
  apply prod_congr rfl
  intro j _
  rw [congrFun (idealSelectedJoin_rest P i p b) j]

theorem idealSelectedProduct_join (P : I → Finset ℕ) (i : I)
    (p : ↥(P i)) (b : IdealSelectedLabels (idealSelectedRest P i)) :
    idealSelectedProduct (idealSelectedJoin P i p b) = p.val * idealSelectedProduct b := by
  unfold idealSelectedProduct
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ i, idealSelectedJoin_at]
  apply congrArg (fun z : ℕ => p.val * z)
  apply prod_congr rfl
  intro j _
  rw [congrFun (idealSelectedJoin_rest P i p b) j]

theorem idealSelectedExpectation_split (P : I → Finset ℕ) (i : I)
    (f : IdealSelectedLabels P → ℂ) :
    (∑ a, (idealSelectedMass P a : ℂ) * f a) =
      ∑ b : IdealSelectedLabels (idealSelectedRest P i),
        (idealSelectedMass (idealSelectedRest P i) b : ℂ) *
          ∑ p : ↥(P i), (markedHarmonicAtom (P i) p : ℂ) * f (idealSelectedJoin P i p b) := by
  rw [← (Equiv.piSplitAt i (fun j => ↥(P j))).symm.sum_comp
    (fun a => (idealSelectedMass P a : ℂ) * f a), Fintype.sum_prod_type, sum_comm]
  apply sum_congr rfl
  intro b _
  rw [mul_sum]
  apply sum_congr rfl
  intro p _
  change (idealSelectedMass P (idealSelectedJoin P i p b) : ℂ) *
    f (idealSelectedJoin P i p b) = _
  rw [idealSelectedMass_join, Complex.ofReal_mul]
  ring

end
end ArtinMatthews
