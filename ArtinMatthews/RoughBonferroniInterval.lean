module

public import ArtinMatthews.RoughBonferroniDivisors
public import ArtinMatthews.MarkedMajorArcDivisorReindex
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
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

/-! Natural-interval mass of the genuine complex Bonferroni remainder. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators Classical
open Finset

/-- Exact number of multiples in an arbitrary natural half-open interval. -/
theorem rough_interval_multiples_sum (M N d : ℕ) (hd : 0 < d) :
    (∑ n ∈ Ioc M N, if d ∣ n then (1 : ℝ) else 0) =
      ((N / d - M / d : ℕ) : ℝ) := by
  rw [marked_sum_Ioc_dvd_reindex hd]
  simp

/-- Interval multiples have their reciprocal-density main term with an
absolute endpoint error at most one, including empty intervals. -/
theorem rough_interval_multiples_le (M N d : ℕ) (hd : 0 < d) :
    (∑ n ∈ Ioc M N, if d ∣ n then (1 : ℝ) else 0) ≤
      ((N - M : ℕ) : ℝ) / d + 1 := by
  rw [rough_interval_multiples_sum M N d hd]
  by_cases hMN : M ≤ N
  · have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have hn : ((N / d : ℕ) : ℝ) * d ≤ N := by
      exact_mod_cast Nat.div_mul_le_self N d
    have hm : (M : ℝ) < (((M / d : ℕ) : ℝ) + 1) * d := by
      have hmod : ((M % d : ℕ) : ℝ) < d := by exact_mod_cast Nat.mod_lt M hd
      have he : (M : ℝ) = ((M / d : ℕ) : ℝ) * d + (M % d : ℕ) := by
        exact_mod_cast (show M = M / d * d + M % d by
          simpa only [Nat.mul_comm] using (Nat.div_add_mod M d).symm)
      nlinarith
    rw [Nat.cast_sub (Nat.div_le_div_right hMN)]
    calc
      _ ≤ ((N : ℝ) - M + d) / d := (le_div_iff₀ hdR).mpr (by nlinarith)
      _ = _ := by rw [Nat.cast_sub hMN, add_div, div_self hdR.ne']
  · have hdiv : N / d ≤ M / d := Nat.div_le_div_right (by omega)
    rw [Nat.sub_eq_zero_of_le hdiv, Nat.cast_zero]
    positivity

/-- Exact divisor counting bounds the total absolute complex truncation
error by the next squarefree layer's reciprocal mass and endpoint count. -/
theorem roughDivisorPolynomial_Ioc_error_le (P : Finset ℕ) (r M N : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) :
    (∑ n ∈ Ioc M N,
      ‖(if ∀ p ∈ P, ¬ p ∣ n then (1 : ℂ) else 0) - roughDivisorPolynomial P r n‖) ≤
      ((N - M : ℕ) : ℝ) *
        (∑ S ∈ P.powersetCard (r + 1), 1 / (roughSubsetDivisor S : ℝ)) +
      ((P.powersetCard (r + 1)).card : ℝ) := by
  calc
    _ ≤ ∑ n ∈ Ioc M N, ∑ S ∈ P.powersetCard (r + 1),
        if roughSubsetDivisor S ∣ n then (1 : ℝ) else 0 := by
      apply sum_le_sum
      intro n _
      exact roughDivisorPolynomial_error_le P r n hprime
    _ = ∑ S ∈ P.powersetCard (r + 1), ∑ n ∈ Ioc M N,
        if roughSubsetDivisor S ∣ n then (1 : ℝ) else 0 := sum_comm
    _ ≤ ∑ S ∈ P.powersetCard (r + 1),
        (((N - M : ℕ) : ℝ) / (roughSubsetDivisor S : ℝ) + 1) := by
      apply sum_le_sum
      intro S hS
      exact rough_interval_multiples_le M N _
        (roughSubsetDivisor_pos S (fun p hp => hprime p ((mem_powersetCard.mp hS).1 hp)))
    _ = _ := by
      rw [sum_add_distrib, mul_sum]
      simp only [sum_const, nsmul_eq_mul, mul_one]
      congr 1
      apply sum_congr rfl
      intro S _
      ring

/-- The actual truncation can be inserted into any complex oscillatory sum
whose individual weights have norm at most one. -/
theorem roughDivisorPolynomial_weighted_Ioc_error_le
    (P : Finset ℕ) (r M N : ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (a : ℕ → ℂ) (ha : ∀ n ∈ Ioc M N, ‖a n‖ ≤ 1) :
    ‖(∑ n ∈ Ioc M N, (if ∀ p ∈ P, ¬ p ∣ n then (1 : ℂ) else 0) * a n) -
      ∑ n ∈ Ioc M N, roughDivisorPolynomial P r n * a n‖ ≤
      ((N - M : ℕ) : ℝ) *
        (∑ S ∈ P.powersetCard (r + 1), 1 / (roughSubsetDivisor S : ℝ)) +
      ((P.powersetCard (r + 1)).card : ℝ) := by
  rw [← sum_sub_distrib]
  simp_rw [← sub_mul]
  apply (norm_sum_le _ _).trans
  apply le_trans _ (roughDivisorPolynomial_Ioc_error_le P r M N hprime)
  apply sum_le_sum
  intro n hn
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left (ha n hn) (norm_nonneg _)).trans_eq (mul_one _)

end ArtinMatthews
