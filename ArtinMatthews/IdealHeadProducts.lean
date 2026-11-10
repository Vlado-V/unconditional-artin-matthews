module

public import ArtinMatthews.IdealRawPattern
public import ArtinMatthews.IdealHeadTail
public import ArtinMatthews.IdealPhaseFactor
public import ArtinMatthews.IdealSelectedFill
public import ArtinMatthews.IdealPatternProducts
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

/-! All dilation and selected products are unchanged by passing to
the first-slot vector. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealCopiedProduct_head {G : Type*} [Fintype G]
    {P : G → Finset ℕ} {k ell : ℕ} (C : G → Finset (Fin k))
    (a : MarkedPhysicalMarking P (k+ell)) :
    giantTwoSidedPatternCopiedProduct C a=
      giantTwoSidedPatternCopiedProduct (ell:=0) C (idealLabelHead a) := by
  unfold giantTwoSidedPatternCopiedProduct
  apply prod_congr rfl
  intro g _
  apply prod_congr rfl
  intro i _
  rfl

theorem idealSelectedProduct_head {G : Type*} {P : G → Finset ℕ} {k ell : ℕ}
    (S : Finset (G × Fin k)) (a : MarkedPhysicalMarking P (k+ell)) :
    idealResidualSelectedMarking S a=idealFullSelectedLabels S (idealLabelHead a) := rfl

theorem idealCopiedProduct_fill {G : Type*} [Fintype G] [DecidableEq G]
    {P : G → Finset ℕ} {k : ℕ} (S : Finset (G × Fin k))
    (a : MarkedPhysicalMarking P k) (x : IdealSelectedLabels (idealResidualBands P S)) :
    giantTwoSidedPatternCopiedProduct (ell:=0) (idealResidualFreeSlots S) (idealSelectedFill S a x)=
      giantTwoSidedPatternCopiedProduct (ell:=0) (idealResidualFreeSlots S) a := by
  apply giantTwoSidedPatternCopiedProduct_eq
  intro g i hi
  have hn : (g,i)∉S := (mem_idealResidualFreeSlots S g i).not.mp hi
  have hi₀ : Fin.castAdd 0 i=i := Fin.ext rfl
  rw [hi₀]
  simp [idealSelectedFill,idealFlattenLabels,finiteProductFill,hn]


theorem idealRawPhase_selected {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (A B : Finset (G × Fin k)) (hAB : Disjoint A B)
    (Θ ζ : ℝ) (a : MarkedPhysicalMarking P (k+ell)) :
    idealRawPhase Θ ζ a=
      (giantTwoSidedPatternCopiedProduct (idealResidualFreeSlots (A ∪ B)) a:ℂ)^((ζ:ℂ)*Complex.I)*
        idealProductPhase ζ (Θ*(giantTwoSidedPatternCopiedProduct (idealResidualFreeSlots (A ∪ B)) a:ℝ))
          (idealSelectedProduct (idealResidualSelectedMarking A a))
          (idealSelectedProduct (idealResidualSelectedMarking B a)) := by
  change idealDilationPhase Θ ζ (giantTwoSidedPatternCopiedProduct (fun _ => (∅ : Finset (Fin k))) a)= _
  rw [idealResidual_copied_product P A B hAB]
  exact idealDilationPhase_selected Θ ζ _ _ _

end
end ArtinMatthews
