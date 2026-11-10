module

public import ArtinMatthews.GiantComparisonSeparatedSum
public import ArtinMatthews.GiantComparisonNumberedMarks
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! Separate the two free tests against the independent restored marking
measure. The source reciprocal masses and both endpoint dampings survive. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section

variable {J : Type*} [Fintype J] [DecidableEq J] {k ell : ℕ}
  {P : J → Finset ℕ} {C : J → Finset (Fin k)}

theorem giantComparisonIndependentPair_eq_markWeights
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    (L : GiantComparisonListCoefficient P C ell)
    (aux : GiantTwoSidedPatternAuxiliary P C) (q : ℝ) (w w' : ℕ)
    (s t : ((j : J) → Fin (ell+(C j).card) → ℕ) → ℂ)
    (hL : ∀ b b', L b b' aux = s (giantComparisonNumberedFreeList P C ell b) *
      t (giantComparisonNumberedFreeList P C ell b')) :
    ((giantTwoSidedPatternFreshMass P C ell)^2:ℝ) *
        giantComparisonIndependentPair L aux q w w' =
      sourceComparisonMarkWeight P (fun j => ell+(C j).card) (fun _ => q) s w *
        sourceComparisonMarkWeight P (fun j => ell+(C j).card) (fun _ => q) t w' := by
  rw [sourceComparisonMarkWeight_eq_freeMarking_sum P hdis C ell q s w,
    sourceComparisonMarkWeight_eq_freeMarking_sum P hdis C ell q t w']
  simp only [giantComparisonIndependentPair, giantComparisonIndependentDamping, hL,
    Complex.ofReal_mul, Complex.ofReal_pow, ← mul_sum, ← sum_mul]
  ring

end
end ArtinMatthews
