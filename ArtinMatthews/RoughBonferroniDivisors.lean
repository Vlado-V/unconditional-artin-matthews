module

public import ArtinMatthews.RoughBonferroni
public import ArtinMatthews.DivisorBound
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
public import OAI.NumberTheory.Jacobsthal.Sieve.IntervalBoundingSieve


set_option backward.privateInPublic true
@[expose] public section

/-! Actual squarefree divisor indexing of the complex Bonferroni polynomial
and its reciprocal coefficient mass. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators Classical
open Finset

def roughSubsetDivisor (S : Finset ℕ) : ℕ := ∏ p ∈ S, p

theorem roughSubsetDivisor_dvd_iff (S : Finset ℕ) (n : ℕ)
    (hprime : ∀ p ∈ S, p.Prime) :
    roughSubsetDivisor S ∣ n ↔ ∀ p ∈ S, p ∣ n := by
  constructor
  · intro h p hp
    exact (dvd_prod_of_mem (fun p : ℕ => p) hp).trans h
  · intro h
    by_cases hn : n = 0
    · simp [hn]
    exact prod_primes_dvd_of_dvd hn hprime h

theorem roughSubsetDivisor_pos (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime) :
    0 < roughSubsetDivisor S :=
  Finset.prod_pos (fun p hp => (hprime p hp).pos)

theorem roughSubsetDivisor_squarefree (S : Finset ℕ)
    (hprime : ∀ p ∈ S, p.Prime) : Squarefree (roughSubsetDivisor S) :=
  OAI.Erdos970.NumberTheoryLean.IntervalBoundingSieve.squarefree_primeSet_product S hprime

def roughDivisorPolynomial (P : Finset ℕ) (r n : ℕ) : ℂ :=
  ∑ S ∈ roughTruncationSubsets P r,
    if roughSubsetDivisor S ∣ n then (-1 : ℂ) ^ S.card else 0

theorem roughDivisorPolynomial_eq (P : Finset ℕ) (r n : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) :
    roughDivisorPolynomial P r n = roughSubsetPolynomial P r (fun p => p ∣ n) := by
  unfold roughDivisorPolynomial roughSubsetPolynomial
  apply sum_congr rfl
  intro S hS
  have hSP : S ⊆ P := mem_powerset.mp (mem_filter.mp hS).1
  simp only [roughSubsetDivisor_dvd_iff S n (fun p hp => hprime p (hSP hp))]
  split_ifs <;> rfl

/-- Literal prime-avoidance indicator minus the actual complex divisor
polynomial, bounded pointwise by the next squarefree divisor layer. -/
theorem roughDivisorPolynomial_error_le (P : Finset ℕ) (r n : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) :
    ‖(if ∀ p ∈ P, ¬ p ∣ n then (1 : ℂ) else 0) - roughDivisorPolynomial P r n‖ ≤
      ∑ S ∈ P.powersetCard (r + 1), if roughSubsetDivisor S ∣ n then (1 : ℝ) else 0 := by
  have hs : (if ∀ p ∈ P, ¬ p ∣ n then (1 : ℂ) else 0) =
      (OAI.Erdos970.NumberTheoryLean.BonferroniBlocks.survives P (fun p => p ∣ n) : ℂ) := by
    simp only [OAI.Erdos970.NumberTheoryLean.BonferroniBlocks.survives]
    split_ifs <;> simp
  rw [hs, roughDivisorPolynomial_eq P r n hprime, roughSubsetPolynomial_eq_real,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  apply (real_bonferroni_error_le P r (fun p => p ∣ n)).trans_eq
  apply sum_congr rfl
  intro S hS
  simp only [OAI.Erdos970.NumberTheoryLean.BonferroniBlocks.intersectionValue,
    roughSubsetDivisor_dvd_iff S n
      (fun p hp => hprime p ((mem_powersetCard.mp hS).1 hp))]
  split_ifs <;> rfl

/-- All actual complex coefficients have reciprocal mass bounded by the
full finite Euler product; the raw number of subsets does not appear. -/
theorem roughDivisorPolynomial_reciprocal_mass_le (P : Finset ℕ) (r : ℕ) :
    (∑ S ∈ roughTruncationSubsets P r,
      ‖(-1 : ℂ) ^ S.card‖ / (roughSubsetDivisor S : ℝ)) ≤
        ∏ p ∈ P, (1 + (p : ℝ)⁻¹) := by
  simp only [norm_pow, norm_neg, norm_one, one_pow, one_div]
  rw [prod_one_add]
  calc
    _ ≤ ∑ S ∈ P.powerset, (roughSubsetDivisor S : ℝ)⁻¹ := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intro S _ _
      positivity
    _ = _ := by
      apply sum_congr rfl
      intro S _
      simp [roughSubsetDivisor]

end ArtinMatthews
