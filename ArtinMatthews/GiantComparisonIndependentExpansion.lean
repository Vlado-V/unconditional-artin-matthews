module

public import ArtinMatthews.GiantComparisonNumberedMarks
public import ArtinMatthews.GiantComparisonSeparatedSum
public import ArtinMatthews.GiantComparisonIndependentCell
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

/-! A finite character-cell decomposition can be exchanged with the
two original ordered marking sums before any analytic estimate. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section

variable {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I]
  {k ell : ℕ} {P : J → Finset ℕ} {C : J → Finset (Fin k)}

theorem giantComparisonIndependentPair_eq_cell_expansion
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    (L : GiantComparisonListCoefficient P C ell)
    (aux : GiantTwoSidedPatternAuxiliary P C) (q : ℝ) (w w' : ℕ)
    (c : I → ℂ) (s t : I → ((j : J) → Fin (ell+(C j).card) → ℕ) → ℂ)
    (hL : ∀ b b', L b b' aux =
      ∑ i, c i * (s i (giantComparisonNumberedFreeList P C ell b) *
        t i (giantComparisonNumberedFreeList P C ell b'))) :
    ((giantTwoSidedPatternFreshMass P C ell)^2:ℝ) *
        giantComparisonIndependentPair L aux q w w' =
      ∑ i, c i *
        (sourceComparisonMarkWeight P (fun j => ell+(C j).card) (fun _ => q) (s i) w *
          sourceComparisonMarkWeight P (fun j => ell+(C j).card) (fun _ => q) (t i) w') := by
  let L' (i : I) : GiantComparisonListCoefficient P C ell := fun b b' _ =>
    s i (giantComparisonNumberedFreeList P C ell b) *
      t i (giantComparisonNumberedFreeList P C ell b')
  have hs : giantComparisonIndependentPair L aux q w w' =
      ∑ i, c i * giantComparisonIndependentPair (L' i) aux q w w' := by
    simp only [giantComparisonIndependentPair, hL, L', mul_sum]
    simp_rw [sum_comm (s := (univ : Finset (GiantComparisonFreeMarking P C ell w')))
      (t := (univ : Finset I))]
    rw [sum_comm (s := (univ : Finset (GiantComparisonFreeMarking P C ell w)))
      (t := (univ : Finset I))]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro b _
    apply sum_congr rfl
    intro b' _
    ring
  rw [hs, mul_sum]
  apply sum_congr rfl
  intro i _
  rw [← giantComparisonIndependentPair_eq_markWeights hdis (L' i) aux q w w' (s i) (t i)
    (fun _ _ => rfl)]
  ring

end
end ArtinMatthews
