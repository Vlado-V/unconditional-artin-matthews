module

public import ArtinMatthews.DivisorWeights
public import ArtinMatthews.MarkedProgressionIndexed
public import OAI.NumberTheory.Jacobsthal.Analysis.BonferroniDensity
public import ArtinMatthews.MarkedProgressionExpansion
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
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Weighted residuals on a union of disjoint marking bands. The damping
may vary from prime to prime, allowing ordinary and repeated bands in one
Bonferroni expansion. -/

namespace ArtinMatthews

open OAI.Erdos970.NumberTheoryLean
open scoped BigOperators

noncomputable def markedWeightedInput (u : ℕ) (θ : ℕ → ℝ) (p : ℕ) : ℝ :=
  θ p * (if p ∣ u then 1 else 0)

noncomputable def markedWeightedResidual (P S : Finset ℕ) (θ : ℕ → ℝ) (u : ℕ) : ℝ :=
  if S ⊆ activeDivisors P u then
    ∏ p ∈ P \ S, (1 - markedWeightedInput u θ p)
  else 0

noncomputable def markedWeightedTail (P S : Finset ℕ) (θ : ℕ → ℝ) (k u : ℕ) : ℝ :=
  markedIndexedDivisorPolynomial ((P \ S).powersetCard k)
    (fun T => ∏ p ∈ S ∪ T, p) (fun T => ∏ p ∈ T, θ p) u

noncomputable def markedWeightedTruncation (P S : Finset ℕ) (θ : ℕ → ℝ) (k u : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), (-1 : ℝ) ^ j * markedWeightedTail P S θ j u

/-- Product indicators keep exactly one copy of each prime. -/
theorem marked_weighted_hit_product (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (u : ℕ) (θ : ℕ → ℝ) :
    (∏ p ∈ P, markedWeightedInput u θ p) =
      if (∏ p ∈ P, p) ∣ u then ∏ p ∈ P, θ p else 0 := by
  classical
  by_cases h : (∏ p ∈ P, p) ∣ u
  · have hh := (marked_prime_product_dvd_iff P hP u).mp h
    rw [ite_eq_left h]
    apply Finset.prod_congr rfl
    intro p hp
    simp only [markedWeightedInput, ite_eq_left (hh p hp), mul_one]
  · rw [ite_eq_right h]
    have hn := (marked_prime_product_dvd_iff P hP u).not.mp h
    push Not at hn
    obtain ⟨p, hp, hpu⟩ := hn
    exact Finset.prod_eq_zero hp (by simp [markedWeightedInput, hpu])

theorem marked_weighted_selected_hit_product (P S T : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hS : S ⊆ P) (hT : T ⊆ P) (u : ℕ) (θ : ℕ → ℝ) :
    (if S ⊆ activeDivisors P u then ∏ p ∈ T, markedWeightedInput u θ p else 0) =
      if (∏ p ∈ S ∪ T, p) ∣ u then ∏ p ∈ T, θ p else 0 := by
  classical
  have hs : S ⊆ activeDivisors P u ↔ ∀ p ∈ S, p ∣ u := by
    simp only [activeDivisors, Finset.subset_iff, Finset.mem_filter]
    exact ⟨fun h p hp => (h hp).2, fun h p hp => ⟨hS hp, h p hp⟩⟩
  have hprime : ∀ p ∈ S ∪ T, p.Prime := fun p hp => hP p
    (Finset.mem_union.mp hp |>.elim (fun h => hS h) (fun h => hT h))
  rw [marked_weighted_hit_product T (fun p hp => hP p (hT hp)) u θ]
  simp only [marked_prime_product_dvd_iff _ hprime, marked_prime_product_dvd_iff T
    (fun p hp => hP p (hT hp)), Finset.forall_mem_union, hs]
  split_ifs <;> simp_all

theorem markedWeightedTail_eq (P S : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hS : S ⊆ P) (θ : ℕ → ℝ) (k u : ℕ) :
    markedWeightedTail P S θ k u = if S ⊆ activeDivisors P u then
      BonferroniDensity.elementarySum (P \ S) (markedWeightedInput u θ) k else 0 := by
  classical
  unfold markedWeightedTail markedIndexedDivisorPolynomial BonferroniDensity.elementarySum
  symm
  have hif : (if S ⊆ activeDivisors P u then
      ∑ T ∈ (P \ S).powersetCard k, ∏ p ∈ T, markedWeightedInput u θ p else 0) =
      ∑ T ∈ (P \ S).powersetCard k, if S ⊆ activeDivisors P u then
        ∏ p ∈ T, markedWeightedInput u θ p else 0 := by
    by_cases hs : S ⊆ activeDivisors P u <;> simp [hs]
  rw [hif]
  apply Finset.sum_congr rfl
  intro T hT
  exact marked_weighted_selected_hit_product P S T hP hS
    (fun _ hp => (Finset.mem_sdiff.mp ((Finset.mem_powersetCard.mp hT).1 hp)).1) u θ

theorem markedWeightedTruncation_eq (P S : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hS : S ⊆ P) (θ : ℕ → ℝ) (k u : ℕ) :
    markedWeightedTruncation P S θ k u = if S ⊆ activeDivisors P u then
      BonferroniDensity.densityPolynomial k (P \ S) (markedWeightedInput u θ) else 0 := by
  classical
  unfold markedWeightedTruncation
  simp_rw [markedWeightedTail_eq P S hP hS]
  by_cases hs : S ⊆ activeDivisors P u <;>
    simp [hs, BonferroniDensity.densityPolynomial]

/-- The upper truncation has a positive omitted tail, uniformly in all
prime-dependent damping choices in `[0,1]`. -/
theorem markedWeightedTruncation_error (P S : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hS : S ⊆ P) (θ : ℕ → ℝ) (hθ : ∀ p ∈ P, 0 ≤ θ p ∧ θ p ≤ 1) (m u : ℕ) :
    0 ≤ markedWeightedTruncation P S θ (2 * m) u - markedWeightedResidual P S θ u ∧
      markedWeightedTruncation P S θ (2 * m) u - markedWeightedResidual P S θ u ≤
        markedWeightedTail P S θ (2 * m + 1) u := by
  classical
  rw [markedWeightedTruncation_eq P S hP hS, markedWeightedTail_eq P S hP hS]
  unfold markedWeightedResidual
  by_cases hs : S ⊆ activeDivisors P u
  · simp only [ite_eq_left hs]
    have hb (p : ℕ) (hp : p ∈ P \ S) :
        0 ≤ markedWeightedInput u θ p ∧ markedWeightedInput u θ p ≤ 1 := by
      have hp' := hθ p (Finset.mem_sdiff.mp hp).1
      unfold markedWeightedInput
      split_ifs <;> simp_all
    have h := BonferroniDensity.densityPolynomial_bounds (P \ S) (markedWeightedInput u θ)
      (fun p hp => (hb p hp).1) (fun p hp => (hb p hp).2) m
    have hg := BonferroniDensity.densityPolynomial_gap m (P \ S) (markedWeightedInput u θ)
    constructor <;> linarith [h.1, h.2]
  · simp [hs]

/-- The reciprocal mass factorization allows prime-dependent damping. -/
theorem marked_weighted_selected_reciprocal_mass (P S : Finset ℕ) (k : ℕ) (θ : ℕ → ℝ) :
    (∑ T ∈ (P \ S).powersetCard k, (∏ p ∈ T, θ p) / (∏ p ∈ S ∪ T, p : ℕ)) =
      (1 / (∏ p ∈ S, p : ℕ)) *
        BonferroniDensity.elementarySum (P \ S) (fun p => θ p / (p : ℝ)) k := by
  classical
  unfold BonferroniDensity.elementarySum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  have hdis : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro p hp hpT
    exact (Finset.mem_sdiff.mp ((Finset.mem_powersetCard.mp hT).1 hpT)).2 hp
  rw [Finset.prod_union hdis, Nat.cast_mul, Finset.prod_div_distrib]
  simp only [Nat.cast_prod]
  ring

end ArtinMatthews
