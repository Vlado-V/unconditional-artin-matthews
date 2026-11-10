module

public import ArtinMatthews.MarkedTypeIIPadCollisions
public import ArtinMatthews.IdealPrimitiveCharacters
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

/-! Selected prime labels retain their original harmonic product law.
The index type can be any finite set of selected source slots. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev IdealSelectedLabels {I : Type*} (P : I → Finset ℕ) := ∀ i, ↥(P i)

def idealSelectedMass {I : Type*} [Fintype I] (P : I → Finset ℕ)
    (a : IdealSelectedLabels P) : ℝ :=
  ∏ i, markedHarmonicAtom (P i) (a i)

def idealSelectedProduct {I : Type*} [Fintype I] {P : I → Finset ℕ}
    (a : IdealSelectedLabels P) : ℕ :=
  ∏ i, (a i).val

theorem idealSelectedMass_nonneg {I : Type*} [Fintype I] (P : I → Finset ℕ)
    (hV : ∀ i, 0 < bandReciprocalMass (P i)) (a : IdealSelectedLabels P) :
    0 ≤ idealSelectedMass P a :=
  prod_nonneg fun i _ => markedHarmonicAtom_nonneg (P i) (hV i)

theorem idealSelectedMass_sum {I : Type*} [Fintype I] [DecidableEq I]
    (P : I → Finset ℕ) (hV : ∀ i, 0 < bandReciprocalMass (P i)) :
    (∑ a : IdealSelectedLabels P, idealSelectedMass P a) = 1 := by
  unfold idealSelectedMass
  rw [← Fintype.prod_sum]
  simp only [markedHarmonicAtom_sum _ (hV _), prod_const_one]

theorem idealSelectedProduct_pos {I : Type*} [Fintype I] {P : I → Finset ℕ}
    (hP : ∀ i p, p ∈ P i → p.Prime) (a : IdealSelectedLabels P) :
    0 < idealSelectedProduct a :=
  prod_pos fun i _ => (hP i (a i).val (a i).property).pos

theorem idealSelectedCharacter_product {I : Type*} [Fintype I]
    {P : I → Finset ℕ} {Q : ℕ} (χ : IdealPrimitiveCharacters Q)
    (a : IdealSelectedLabels P) :
    idealPrimitiveCharacterValue χ (idealSelectedProduct a) =
      ∏ i, idealPrimitiveCharacterValue χ (a i).val := by
  unfold idealPrimitiveCharacterValue idealSelectedProduct
  rw [Nat.cast_prod, map_prod]

theorem idealSelectedCharacter_norm_le {I : Type*} [Fintype I]
    {P : I → Finset ℕ} {Q : ℕ} (χ : IdealPrimitiveCharacters Q)
    (a : IdealSelectedLabels P) :
    ‖idealPrimitiveCharacterValue χ (idealSelectedProduct a)‖ ≤ 1 :=
  idealPrimitiveCharacterValue_norm_le χ _

end
end ArtinMatthews
