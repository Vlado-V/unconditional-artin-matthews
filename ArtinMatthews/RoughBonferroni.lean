module

public import OAI.NumberTheory.Jacobsthal.Estimates.BonferroniBlocks
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite complex Bonferroni truncation, with an absolute pointwise
error controlled by the next intersection layer. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators Classical
open Finset
open OAI.Erdos970.NumberTheoryLean.BonferroniBlocks

/-- Subsets used by the actual order-`r` inclusion-exclusion polynomial. -/
def roughTruncationSubsets (P : Finset ℕ) (r : ℕ) : Finset (Finset ℕ) :=
  P.powerset.filter (fun S => S.card ≤ r)

/-- The subset and cardinal-layer presentations of a finite truncation agree. -/
theorem sum_roughTruncationSubsets {V : Type*} [AddCommMonoid V]
    (P : Finset ℕ) (r : ℕ) (f : Finset ℕ → V) :
    ∑ S ∈ roughTruncationSubsets P r, f S =
      ∑ j ∈ range (r + 1), ∑ S ∈ P.powersetCard j, f S := by
  calc
    _ = ∑ j ∈ range (r + 1),
        ∑ S ∈ (roughTruncationSubsets P r).filter (fun S => S.card = j), f S := by
      refine (sum_fiberwise_of_maps_to ?_ _).symm
      intro S hS
      exact mem_range.mpr (Nat.lt_succ_iff.mpr (mem_filter.mp hS).2)
    _ = _ := by
      apply sum_congr rfl
      intro j hj
      have hjr : j ≤ r := Nat.lt_succ_iff.mp (mem_range.mp hj)
      have hset : (roughTruncationSubsets P r).filter (fun S => S.card = j) =
          P.powersetCard j := by
        ext S
        simp only [roughTruncationSubsets, mem_filter, mem_powerset, mem_powersetCard]
        aesop
      rw [hset]

/-- The literal complex-valued finite inclusion-exclusion polynomial. -/
def roughSubsetPolynomial (P : Finset ℕ) (r : ℕ) (hit : ℕ → Prop) : ℂ :=
  ∑ S ∈ roughTruncationSubsets P r,
    if ∀ p ∈ S, hit p then (-1 : ℂ) ^ S.card else 0

theorem roughSubsetPolynomial_eq_real (P : Finset ℕ) (r : ℕ) (hit : ℕ → Prop) :
    roughSubsetPolynomial P r hit = (coefficientPolynomial r P hit : ℂ) := by
  rw [roughSubsetPolynomial, sum_roughTruncationSubsets]
  simp only [coefficientPolynomial, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one, mul_sum]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro S hS
  rw [(mem_powersetCard.mp hS).2]
  simp only [intersectionValue]
  split_ifs <;> simp

/-- Every truncation order has absolute error at most the next intersection
layer; the proof uses the exact alternating binomial identity. -/
theorem real_bonferroni_error_le (P : Finset ℕ) (r : ℕ) (hit : ℕ → Prop) :
    |survives P hit - coefficientPolynomial r P hit| ≤
      ∑ S ∈ P.powersetCard (r + 1), intersectionValue S hit := by
  rw [survives_eq_zero_count, coefficientPolynomial_eq_alternatingChoose,
    sum_intersectionValue_eq_choose]
  cases h : (hitSet P hit).card with
  | zero => simp [alternatingChoose_zero]
  | succ k =>
      rw [alternatingChoose_succ]
      simp only [Nat.succ_ne_zero, ite_false, zero_sub, abs_neg, abs_mul,
        abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
      exact_mod_cast (show k.choose r ≤ (k + 1).choose (r + 1) by
        rw [Nat.choose_succ_succ]
        omega)

/-- Complex pointwise truncation error, available for oscillatory weights. -/
theorem roughSubsetPolynomial_error_le (P : Finset ℕ) (r : ℕ) (hit : ℕ → Prop) :
    ‖(if ∀ p ∈ P, ¬ hit p then (1 : ℂ) else 0) - roughSubsetPolynomial P r hit‖ ≤
      ∑ S ∈ P.powersetCard (r + 1), if ∀ p ∈ S, hit p then (1 : ℝ) else 0 := by
  have hs : (if ∀ p ∈ P, ¬ hit p then (1 : ℂ) else 0) =
      (survives P hit : ℂ) := by
    simp only [survives]
    split_ifs <;> simp
  rw [hs, roughSubsetPolynomial_eq_real, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs]
  exact real_bonferroni_error_le P r hit

end ArtinMatthews
