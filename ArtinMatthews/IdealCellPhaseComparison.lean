module

public import ArtinMatthews.IdealCellLogVariation
public import ArtinMatthews.IdealPhaseFactor
public import ArtinMatthews.IdealRationalCellIdentity
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

/-! The original complex phase difference is the sum of the rational
character error and the controlled logarithmic phase variation. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

def idealFullCellPhaseAverage (P : A → Finset ℕ) (R : B → Finset ℕ)
    (Q : ℕ) (h ξ ζ α : ℝ) (x : IdealSelectedLabels P) (y : IdealSelectedLabels R) : ℂ :=
  ∑ d : IdealSelectedLabels P, ∑ e : IdealSelectedLabels R,
    (idealSelectedMass P d : ℂ) * idealCharacterCellKernel P Q h ξ d x *
      (idealSelectedMass R e : ℂ) * idealCharacterCellKernel R Q h ξ e y *
        idealProductPhase ζ α (idealSelectedProduct d) (idealSelectedProduct e)

theorem idealCellLogVariation_eq (P : A → Finset ℕ) (R : B → Finset ℕ)
    (hP : ∀ i p, p ∈ P i → p.Prime) (hR : ∀ i p, p ∈ R i → p.Prime)
    (Q r : ℕ) (h ξ ζ β : ℝ) (u : ℤ)
    (x : IdealSelectedLabels P) (y : IdealSelectedLabels R) :
    idealCellLogVariation P R Q r h ξ ζ β u x y =
      idealLogPhase ζ β (Real.log (idealSelectedProduct x) + Real.log (idealSelectedProduct y)) *
        idealRationalCellAverage P R Q r h ξ u x y -
      idealFullCellPhaseAverage P R Q h ξ ζ ((u : ℝ)/r+β) x y := by
  unfold idealCellLogVariation idealRationalCellAverage idealFullCellPhaseAverage
  conv_rhs => rw [mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro d _
  conv_rhs => rw [mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro e _
  rw [idealProductPhase_rational, ← idealLogPhase_product ζ β
    (idealSelectedProduct_pos hP d) (idealSelectedProduct_pos hR e)]
  ring

theorem idealCellPhaseComparison_split (P : A → Finset ℕ) (R : B → Finset ℕ)
    (hP : ∀ i p, p ∈ P i → p.Prime) (hR : ∀ i p, p ∈ R i → p.Prime)
    (Q r : ℕ) (h ξ ζ β : ℝ) (u : ℤ)
    (x : IdealSelectedLabels P) (y : IdealSelectedLabels R) :
    ‖idealProductPhase ζ ((u : ℝ)/r+β) (idealSelectedProduct x) (idealSelectedProduct y) -
      idealFullCellPhaseAverage P R Q h ξ ζ ((u : ℝ)/r+β) x y‖ ≤
      ‖(Real.fourierChar ((u : ℝ)*(idealSelectedProduct x : ℝ)*(idealSelectedProduct y : ℝ)/r) : ℂ) -
        idealRationalCellAverage P R Q r h ξ u x y‖ +
      ‖idealCellLogVariation P R Q r h ξ ζ β u x y‖ := by
  let z := idealLogPhase ζ β (Real.log (idealSelectedProduct x) + Real.log (idealSelectedProduct y))
  let a : ℂ := Real.fourierChar ((u : ℝ)*(idealSelectedProduct x : ℝ)*(idealSelectedProduct y : ℝ)/r)
  let b := idealRationalCellAverage P R Q r h ξ u x y
  have he : idealProductPhase ζ ((u : ℝ)/r+β) (idealSelectedProduct x) (idealSelectedProduct y) -
      idealFullCellPhaseAverage P R Q h ξ ζ ((u : ℝ)/r+β) x y =
      z*(a-b) + idealCellLogVariation P R Q r h ξ ζ β u x y := by
    rw [idealCellLogVariation_eq P R hP hR, idealProductPhase_rational,
      ← idealLogPhase_product ζ β (idealSelectedProduct_pos hP x) (idealSelectedProduct_pos hR y)]
    dsimp only [z, a, b]
    ring
  rw [he]
  refine (norm_add_le _ _).trans_eq ?_
  rw [norm_mul, idealLogPhase_norm, one_mul]

end
end ArtinMatthews
