module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import ArtinMatthews.CubicSieveBlockProducts
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

/-! Finite tail estimates for the actual total-degree truncation. -/

noncomputable section
namespace ArtinMatthews

open Finset
open scoped BigOperators

theorem cubicSieve_quarter_geometric_tail (I : Finset ℕ) (k : ℕ)
    (hI : ∀ j ∈ I, k ≤ j) :
    (∑ j ∈ I, (1 / 4 : ℝ) ^ j) ≤ 2 * (1 / 4 : ℝ) ^ k := by
  have hinj : Set.InjOn (fun j => j - k) (I : Set ℕ) := by
    intro a ha b hb he
    change a - k = b - k at he
    have hka := hI a ha
    have hkb := hI b hb
    omega
  calc
    _ = (1 / 4 : ℝ) ^ k * ∑ j ∈ I.image (fun j => j - k), (1 / 4 : ℝ) ^ j := by
      rw [mul_sum, sum_image hinj]
      apply sum_congr rfl
      intro j hj
      rw [← pow_add, Nat.add_sub_of_le (hI j hj)]
    _ ≤ (1 / 4 : ℝ) ^ k * ∑ j ∈ I.image (fun j => j - k), (1 / 2 : ℝ) ^ j := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact sum_le_sum (fun j _ => pow_le_pow_left₀ (by norm_num) (by norm_num) j)
    _ ≤ _ := (mul_le_mul_of_nonneg_left (cubicSieve_half_geometric_sum _) (by positivity)).trans_eq
      (mul_comm _ _)

theorem cubicSieve_truncation_split (K k : ℕ) (f : ℕ → ℝ)
    (hzero : ∀ j, K < j → f j = 0) :
    (∑ j ∈ range (k + 1), f j) + (∑ j ∈ (range (K + 1)).filter (fun j => k < j), f j) =
      ∑ j ∈ range (K + 1), f j := by
  let I := (range (K + 1)).filter (fun j => j ≤ k)
  have hsub : I ⊆ range (k + 1) := fun j hj =>
    mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp hj).2)
  have he : (∑ j ∈ range (k + 1), f j) = ∑ j ∈ I, f j := by
    symm
    apply sum_subset hsub
    intro j hj hjI
    have hkj : j ≤ k := Nat.le_of_lt_succ (mem_range.mp hj)
    have hlarge : K < j := by
      by_contra! h
      exact hjI (mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le h), hkj⟩)
    exact hzero j hlarge
  rw [he]
  simpa only [I, not_le] using
    sum_filter_add_sum_filter_not (range (K + 1)) (fun j => j ≤ k) f

theorem cubicSieve_truncation_tail_abs_le (K k : ℕ) (f : ℕ → ℝ) {B : ℝ}
    (hB : 0 ≤ B) (hzero : ∀ j, K < j → f j = 0)
    (hbound : ∀ j, |f j| ≤ B * (1 / 4 : ℝ) ^ j) :
    |(∑ j ∈ range (k + 1), f j) - (∑ j ∈ range (K + 1), f j)| ≤
      2 * B * (1 / 4 : ℝ) ^ k := by
  have he := cubicSieve_truncation_split K k f hzero
  have hdiff : (∑ j ∈ range (k + 1), f j) - (∑ j ∈ range (K + 1), f j) =
      -(∑ j ∈ (range (K + 1)).filter (fun j => k < j), f j) := by linarith only [he]
  rw [hdiff, abs_neg]
  calc
    _ ≤ ∑ j ∈ (range (K + 1)).filter (fun j => k < j), |f j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ (range (K + 1)).filter (fun j => k < j), B * (1 / 4 : ℝ) ^ j :=
      sum_le_sum (fun j _ => hbound j)
    _ = B * ∑ j ∈ (range (K + 1)).filter (fun j => k < j), (1 / 4 : ℝ) ^ j := (mul_sum _ _ _).symm
    _ ≤ _ := (mul_le_mul_of_nonneg_left
      (cubicSieve_quarter_geometric_tail _ k (fun j hj => (mem_filter.mp hj).2.le)) hB).trans_eq
      (by ring)

end ArtinMatthews
