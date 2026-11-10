module

public import ArtinMatthews.MarkedProgressionTruncation
public import ArtinMatthews.MarkedProgressionIndexed
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

/-!
# Exact divisor expansions for the retained residual and its positive tail

The index sets remain subsets of the prime band. Thus repeated arrays retain
one selected union and never require an unjustified injectivity assumption.
-/

namespace ArtinMatthews

open OAI.Erdos970.NumberTheoryLean
open scoped BigOperators

/-- A product of distinct primes divides exactly when every prime divides. -/
theorem marked_prime_product_dvd_iff (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (u : ℕ) :
    (∏ p ∈ P, p) ∣ u ↔ ∀ p ∈ P, p ∣ u := by
  constructor
  · intro h p hp
    exact (Finset.dvd_prod_of_mem id hp).trans h
  · intro h
    apply Finset.prod_dvd_of_isRelPrime _ h
    intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hP p hp) (hP q hq)).mpr hpq)

/-- Products of hit indicators are exactly squarefree-divisor indicators. -/
theorem marked_hit_product (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (u : ℕ) (θ : ℝ) :
    (∏ p ∈ P, θ * (if p ∣ u then 1 else 0)) =
      if (∏ p ∈ P, p) ∣ u then θ ^ P.card else 0 := by
  classical
  by_cases h : (∏ p ∈ P, p) ∣ u
  · have hh := (marked_prime_product_dvd_iff P hP u).mp h
    rw [ite_eq_left h]
    rw [Finset.prod_mul_distrib]
    have hone : (∏ p ∈ P, if p ∣ u then (1 : ℝ) else 0) = 1 :=
      Finset.prod_eq_one (fun p hp => ite_eq_left (hh p hp))
    simp [hone]
  · rw [ite_eq_right h]
    have hn := (marked_prime_product_dvd_iff P hP u).not.mp h
    push Not at hn
    obtain ⟨p, hp, hpu⟩ := hn
    exact Finset.prod_eq_zero hp (by simp [hpu])

/-- The positive tail is an explicit indexed divisor polynomial. -/
theorem markedResidualTail_eq_polynomial (P S : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (u a k : ℕ) (ρ : ℝ) :
    markedResidualTail k P S u a ρ =
      markedIndexedDivisorPolynomial ((P \ S).powersetCard k)
        (fun T => ∏ p ∈ T, p) (fun _ => (1 - ρ ^ a) ^ k) u := by
  classical
  unfold markedResidualTail BonferroniDensity.elementarySum markedIndexedDivisorPolynomial
  apply Finset.sum_congr rfl
  intro T hT
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hT
  simpa only [markedResidualInput, hcard] using marked_hit_product T
    (fun p hp => hP p (Finset.mem_sdiff.mp (hsub hp)).1) u (1 - ρ ^ a)

/-- Every retained homogeneous piece is an explicit divisor polynomial. -/
theorem markedResidualTruncation_eq_sum (P S : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (u a k : ℕ) (ρ : ℝ) :
    markedResidualTruncation k P S u a ρ =
      ∑ j ∈ Finset.range (k + 1), (-1 : ℝ) ^ j *
        markedIndexedDivisorPolynomial ((P \ S).powersetCard j)
          (fun T => ∏ p ∈ T, p) (fun _ => (1 - ρ ^ a) ^ j) u := by
  unfold markedResidualTruncation BonferroniDensity.densityPolynomial
  apply Finset.sum_congr rfl
  intro j _
  rw [← markedResidualTail_eq_polynomial P S hP u a j ρ]
  rfl

/-- Selection of the represented set combines with the residual hit set by
set union, so coincident represented primes are counted only once. -/
theorem marked_selected_hit_product (P S T : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hS : S ⊆ P) (hT : T ⊆ P) (u : ℕ) (θ : ℝ) :
    (if S ⊆ activeDivisors P u then (∏ p ∈ T, θ * (if p ∣ u then 1 else 0)) else 0) =
      if (∏ p ∈ S ∪ T, p) ∣ u then θ ^ T.card else 0 := by
  classical
  have hs : S ⊆ activeDivisors P u ↔ ∀ p ∈ S, p ∣ u := by
    simp only [activeDivisors, Finset.subset_iff, Finset.mem_filter]
    exact ⟨fun h p hp => (h hp).2, fun h p hp => ⟨hS hp, h p hp⟩⟩
  have hprime : ∀ p ∈ S ∪ T, p.Prime := fun p hp => hP p
    (Finset.mem_union.mp hp |>.elim (fun h => hS h) (fun h => hT h))
  rw [marked_hit_product T (fun p hp => hP p (hT hp)) u θ]
  simp only [marked_prime_product_dvd_iff _ hprime, marked_prime_product_dvd_iff T
    (fun p hp => hP p (hT hp)), Finset.forall_mem_union, hs]
  split_ifs <;> simp_all

end ArtinMatthews
