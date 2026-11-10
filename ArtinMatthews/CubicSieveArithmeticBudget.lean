module

public import ArtinMatthews.CubicSieveCorrection
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Elementary integer budgets for the genuine squarefree correction
support. No infinite divisor estimate is used. -/

noncomputable section
namespace ArtinMatthews

open Finset
open scoped BigOperators

theorem cubicSieve_two_pow_primeFactors_le {n : ℕ} (hn : 0 < n) :
    (2 : ℕ) ^ n.primeFactors.card ≤ n := by
  have h : (2 : ℕ) ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p := by
    simpa only [prod_const] using
      (prod_le_prod (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le))
  exact h.trans (Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n))

theorem cubicSieve_three_pow_primeFactors_le {n : ℕ} (hn : 0 < n) :
    (3 : ℕ) ^ n.primeFactors.card ≤ 2 * n := by
  let P := n.primeFactors
  have hrad : (∏ p ∈ P, p) ≤ n := Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)
  by_cases h2 : 2 ∈ P
  · have hrest : (3 : ℕ) ^ (P.erase 2).card ≤ ∏ p ∈ P.erase 2, p := by
      simpa only [prod_const] using (prod_le_prod (fun p hp => by
        have hprime := (Nat.prime_of_mem_primeFactors (mem_of_mem_erase hp)).two_le
        have hne := (mem_erase.mp hp).1
        omega : ∀ p ∈ P.erase 2, 3 ≤ p))
    have hc : P.card = (P.erase 2).card + 1 := by
      simpa only [card_insert_of_notMem (notMem_erase 2 P)] using
        congrArg Finset.card (insert_erase h2).symm
    have hp : ∏ p ∈ P, p = 2 * ∏ p ∈ P.erase 2, p := by
      calc
        _ = (∏ p ∈ P.erase 2, p) * 2 := (prod_erase_mul P (fun p : ℕ => p) h2).symm
        _ = _ := Nat.mul_comm _ _
    rw [hc, pow_succ]
    nlinarith only [hrest, hrad, hp]
  · have h : (3 : ℕ) ^ P.card ≤ ∏ p ∈ P, p := by
      simpa only [prod_const] using (prod_le_prod (fun p hp => by
        have hprime := (Nat.prime_of_mem_primeFactors hp).two_le
        have hne : p ≠ 2 := fun h => h2 (h ▸ hp)
        omega : ∀ p ∈ P, 3 ≤ p))
    exact (h.trans hrad).trans (by omega)

theorem cubicSieve_correctionSupport_card {z : ℝ} (m R : ℕ)
    (hR : ∀ S ∈ (Nat.primesLE ⌊z⌋₊).powerset, cubicSieveCorrectionCoeff z m S ≠ 0 →
      roughSubsetDivisor S ≤ R) :
    ((Nat.primesLE ⌊z⌋₊).powerset.filter (fun S => cubicSieveCorrectionCoeff z m S ≠ 0)).card ≤ R := by
  let P := Nat.primesLE ⌊z⌋₊
  let E := P.powerset.filter (fun S => cubicSieveCorrectionCoeff z m S ≠ 0)
  have hP (p : ℕ) (hp : p ∈ P) := Nat.prime_of_mem_primesLE hp
  have hcard : E.card ≤ (Icc 1 R).card := by
    apply card_le_card_of_injOn roughSubsetDivisor
    · intro S hS
      have hh := mem_filter.mp hS
      exact mem_Icc.mpr ⟨roughSubsetDivisor_pos S (fun p hp => hP p (mem_powerset.mp hh.1 hp)),
        hR S hh.1 hh.2⟩
    · exact (OAI.Erdos970.NumberTheoryLean.DisjointBlockExpansion.prime_product_injective P hP).mono
        (fun S hS => (mem_filter.mp hS).1)
  simpa only [Nat.card_Icc, Nat.add_sub_cancel] using hcard

theorem cubicSieve_correctionSupport_weighted_budget {z : ℝ} (m R : ℕ)
    (hR : ∀ S ∈ (Nat.primesLE ⌊z⌋₊).powerset, cubicSieveCorrectionCoeff z m S ≠ 0 →
      roughSubsetDivisor S ≤ R) :
    (∑ S ∈ (Nat.primesLE ⌊z⌋₊).powerset,
      |cubicSieveCorrectionCoeff z m S| * (3 : ℝ) ^ (roughSubsetDivisor S).primeFactors.card) ≤
        2 * (R : ℝ) ^ 2 := by
  let P := Nat.primesLE ⌊z⌋₊
  let E := P.powerset.filter (fun S => cubicSieveCorrectionCoeff z m S ≠ 0)
  have heq : (∑ S ∈ P.powerset,
      |cubicSieveCorrectionCoeff z m S| * (3 : ℝ) ^ (roughSubsetDivisor S).primeFactors.card) =
      ∑ S ∈ E, |cubicSieveCorrectionCoeff z m S| * (3 : ℝ) ^ (roughSubsetDivisor S).primeFactors.card := by
    symm
    apply sum_subset (filter_subset _ _)
    intro S hS hn
    have hz : cubicSieveCorrectionCoeff z m S = 0 := by
      by_contra h
      exact hn (mem_filter.mpr ⟨hS, h⟩)
    simp only [hz, abs_zero, zero_mul]
  rw [heq]
  calc
    _ ≤ ∑ _S ∈ E, 2 * (R : ℝ) := by
      apply sum_le_sum
      intro S hS
      obtain ⟨hSP, hne⟩ := mem_filter.mp hS
      have hpos := roughSubsetDivisor_pos S (fun p hp =>
        Nat.prime_of_mem_primesLE (mem_powerset.mp hSP hp))
      have h3 : (3 : ℝ) ^ (roughSubsetDivisor S).primeFactors.card ≤ 2 * (R : ℝ) := by
        exact_mod_cast (cubicSieve_three_pow_primeFactors_le hpos).trans
          (Nat.mul_le_mul_left 2 (hR S hSP hne))
      exact (mul_le_mul_of_nonneg_right (cubicSieve_correctionCoeff_abs_le z m S)
        (by positivity)).trans (by simpa only [one_mul] using h3)
    _ = (E.card : ℝ) * (2 * (R : ℝ)) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := (mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr (cubicSieve_correctionSupport_card m R hR)) (by positivity)).trans_eq (by ring)

end ArtinMatthews
