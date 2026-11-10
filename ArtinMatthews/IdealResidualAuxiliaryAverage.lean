module

public import ArtinMatthews.IdealPatternProducts
public import ArtinMatthews.IdealAuxiliarySelected
public import ArtinMatthews.IdealCellPhaseComparison
public import ArtinMatthews.IdealSelectedUnion
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

/-! The original auxiliary law, after the copied labels are fixed,
is exactly the two independent character-cell averages. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealAuxiliaryUnion_first {G : Type*} [DecidableEq G]
    (P : G → Finset ℕ) {k : ℕ} (A B : Finset (G × Fin k)) (hAB : Disjoint A B)
    (x : IdealSelectedLabels (idealResidualBands P A))
    (y : IdealSelectedLabels (idealResidualBands P B)) :
    idealResidualSelectedAuxiliary A
      (fun v hv => (mem_idealResidualFreeSlots (A ∪ B) v.1 v.2).mpr (mem_union_left B hv))
      ((idealAuxiliarySelectedEquiv P (A ∪ B)).symm ((idealSelectedUnionEquiv P A B hAB).symm (x,y)))=x := by
  funext v
  change (if h : v.val∈A then x ⟨v.val,h⟩ else y ⟨v.val,False.elim (h v.property)⟩)=x v
  exact dite_eq_left v.property

theorem idealAuxiliaryUnion_second {G : Type*} [DecidableEq G]
    (P : G → Finset ℕ) {k : ℕ} (A B : Finset (G × Fin k)) (hAB : Disjoint A B)
    (x : IdealSelectedLabels (idealResidualBands P A))
    (y : IdealSelectedLabels (idealResidualBands P B)) :
    idealResidualSelectedAuxiliary B
      (fun v hv => (mem_idealResidualFreeSlots (A ∪ B) v.1 v.2).mpr (mem_union_right A hv))
      ((idealAuxiliarySelectedEquiv P (A ∪ B)).symm ((idealSelectedUnionEquiv P A B hAB).symm (x,y)))=y := by
  funext v
  have hv : v.val∉A := fun h => disjoint_left.mp hAB h v.property
  change (if h : v.val∈A then x ⟨v.val,h⟩ else y ⟨v.val,v.property⟩)=y v
  exact dite_eq_right hv

theorem idealResidual_auxiliary_average {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (A B : Finset (G × Fin k)) (hAB : Disjoint A B)
    (Q : ℕ) (h ξ Θ ζ : ℝ) (a : MarkedPhysicalMarking P (k+ell)) :
    (∑ aux : GiantTwoSidedPatternAuxiliary P (idealResidualFreeSlots (A ∪ B)),
      (giantTwoSidedPatternAuxiliaryMass aux:ℂ)*
        idealResidualCoefficient P Q h ξ (some (A,B)) a a aux*
        idealDilationPhase Θ ζ (giantTwoSidedPatternCopiedProduct (idealResidualFreeSlots (A ∪ B)) a*
          giantTwoSidedPatternAuxiliaryProduct aux))=
      -(-1:ℂ)^(A.card+B.card)*
        (giantTwoSidedPatternCopiedProduct (idealResidualFreeSlots (A ∪ B)) a:ℂ)^((ζ:ℂ)*Complex.I)*
        idealFullCellPhaseAverage (idealResidualBands P A) (idealResidualBands P B) Q h ξ ζ
          (Θ*(giantTwoSidedPatternCopiedProduct (idealResidualFreeSlots (A ∪ B)) a:ℝ))
          (idealResidualSelectedMarking A a) (idealResidualSelectedMarking B a) := by
  simp only [mul_assoc]
  rw [idealAuxiliarySelected_expectation P (A ∪ B),idealSelectedUnion_expectation P A B hAB]
  unfold idealFullCellPhaseAverage
  simp only [mul_sum]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro y _
  rw [idealAuxiliarySelected_product,Equiv.apply_symm_apply,idealSelectedUnion_product P A B hAB,
    Equiv.apply_symm_apply,idealDilationPhase_selected]
  dsimp only [idealResidualCoefficient,idealResidualCopied]
  rw [idealAuxiliaryUnion_first P A B hAB,idealAuxiliaryUnion_second P A B hAB]
  ring

end
end ArtinMatthews
