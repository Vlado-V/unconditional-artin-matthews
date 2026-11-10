module

public import ArtinMatthews.MarkedTypeIICoefficients
public import ArtinMatthews.RoughBonferroniDivisors
public import ArtinMatthews.CubicSieveTopBlocks
public import OAI.NumberTheory.Jacobsthal.Estimates.DisjointBlockExpansion
public import ArtinMatthews.CubicSieveBlockLevel
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
public import Mathlib.Tactic.ENatToNat
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

/-! The literal Section 7 upper and overflow polynomials at even depth
h=2m, with a proved squarefree divisor expansion. -/

noncomputable section
namespace ArtinMatthews

open OAI.Erdos970.NumberTheoryLean
open scoped BigOperators Classical

def cubicSieveOrder (m j : ℕ) : ℕ := (j + 1) * m

def cubicSieveUpper (z : ℝ) (m n : ℕ) : ℝ :=
  BonferroniBlocks.blockUpper (cubicSieveBlockIndices z) (cubicSieveBlock z)
    (cubicSieveOrder m) (fun p => p ∣ n)

def cubicSieveCorrection (z : ℝ) (m n : ℕ) : ℝ :=
  BonferroniBlocks.blockCorrection (cubicSieveBlockIndices z) (cubicSieveBlock z)
    (cubicSieveOrder m) (fun p => p ∣ n)

def cubicSieveUpperCoeff (z : ℝ) (m : ℕ) (T : Finset ℕ) : ℝ :=
  DisjointBlockExpansion.upperCoefficient (cubicSieveBlockIndices z) (cubicSieveBlock z)
    (cubicSieveOrder m) T

def cubicSieveUpperSupport (z : ℝ) (m : ℕ) : Finset (Finset ℕ) :=
  (Nat.primesLE ⌊z⌋₊).powerset.filter (fun T => cubicSieveUpperCoeff z m T ≠ 0)

theorem cubicSieve_upperCoeff_abs_le (z : ℝ) (m : ℕ) (T : Finset ℕ) :
    |cubicSieveUpperCoeff z m T| ≤ 1 :=
  DisjointBlockExpansion.upperCoefficient_abs_le _ _ _ _

theorem cubicSieve_upperSupport_level {z : ℝ} (hz : 1 < z) {m : ℕ} {T : Finset ℕ}
    (hT : T ∈ cubicSieveUpperSupport z m) :
    0 < roughSubsetDivisor T ∧ Squarefree (roughSubsetDivisor T) ∧
      (roughSubsetDivisor T : ℝ) ≤ z ^ (8 * (m : ℝ)) := by
  obtain ⟨hsub, hc⟩ := Finset.mem_filter.mp hT
  have hT' := Finset.mem_powerset.mp hsub
  have hp (p : ℕ) (hp : p ∈ T) : p.Prime := (Nat.mem_primesLE.mp (hT' hp)).2
  refine ⟨roughSubsetDivisor_pos T hp, roughSubsetDivisor_squarefree T hp, ?_⟩
  have hb (j : ℕ) (hj : j ∈ cubicSieveBlockIndices z) :
      (T ∩ cubicSieveBlock z j).card ≤ 2 * m * (j + 1) + 0 := by
    have h := DisjointBlockExpansion.upperCoefficient_card hc j hj
    simpa only [cubicSieveOrder, Nat.mul_comm (j + 1) m, Nat.mul_assoc, Nat.add_zero] using h
  simpa only [roughSubsetDivisor, Nat.cast_zero, mul_zero, add_zero] using
    cubicSieve_block_product_level hz hT' m 0 hb

theorem cubicSieve_intersection_eq_divisor (T : Finset ℕ) (n : ℕ)
    (hp : ∀ p ∈ T, p.Prime) :
    BonferroniBlocks.intersectionValue T (fun p => p ∣ n) =
      if roughSubsetDivisor T ∣ n then 1 else 0 := by
  have h := roughSubsetDivisor_dvd_iff T n hp
  by_cases hd : roughSubsetDivisor T ∣ n
  · simp only [BonferroniBlocks.intersectionValue, ite_eq_left hd, ite_eq_left (h.mp hd)]
  · simp only [BonferroniBlocks.intersectionValue, ite_eq_right hd,
      ite_eq_right (fun ht => hd (h.mpr ht))]

theorem cubicSieve_upper_eq_divisor_sum (z : ℝ) (m n : ℕ) :
    cubicSieveUpper z m n =
      ∑ T ∈ cubicSieveUpperSupport z m, if roughSubsetDivisor T ∣ n then cubicSieveUpperCoeff z m T else 0 := by
  have hdis : (cubicSieveBlockIndices z : Set ℕ).Pairwise fun i j =>
      Disjoint (cubicSieveBlock z i) (cubicSieveBlock z j) :=
    fun i _ j _ hij => cubicSieveBlock_disjoint z hij
  unfold cubicSieveUpper
  rw [← DisjointBlockExpansion.upperCoefficient_evaluation _ _ hdis (cubicSieveOrder m)
    (fun p => p ∣ n), cubicSieveBlock_union, cubicSieveUpperSupport, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T hT
  have hp (p : ℕ) (hp : p ∈ T) : p.Prime :=
    (Nat.mem_primesLE.mp (Finset.mem_powerset.mp hT hp)).2
  rw [cubicSieve_intersection_eq_divisor T n hp]
  change cubicSieveUpperCoeff z m T * (if roughSubsetDivisor T ∣ n then 1 else 0) = _
  by_cases hc : cubicSieveUpperCoeff z m T = 0
  · simp [hc]
  · by_cases hd : roughSubsetDivisor T ∣ n
    · simp only [ite_eq_left hc, ite_eq_left hd, mul_one]
    · simp only [ite_eq_right hd, mul_zero, ite_self]

theorem cubicSieve_survives_eq_rough {z : ℝ} (hz : 0 ≤ z) (n : ℕ) :
    BonferroniBlocks.survives (Nat.primesLE ⌊z⌋₊) (fun p => p ∣ n) =
      if MarkedRoughAbove z n then 1 else 0 := by
  have h : (∀ p ∈ Nat.primesLE ⌊z⌋₊, ¬ p ∣ n) ↔ MarkedRoughAbove z n := by
    constructor
    · intro h p hp hd
      by_contra! hpz
      exact h p (Nat.mem_primesLE.mpr ⟨Nat.le_floor hpz, hp⟩) hd
    · intro h p hp hd
      obtain ⟨hcap, hp⟩ := Nat.mem_primesLE.mp hp
      exact (not_lt_of_ge ((Nat.cast_le.mpr hcap).trans (Nat.floor_le hz))) (h p hp hd)
  unfold BonferroniBlocks.survives
  simp only [h]

theorem cubicSieve_upper_rough_error {z : ℝ} (hz : 0 ≤ z) (m n : ℕ) :
    0 ≤ cubicSieveUpper z m n - (if MarkedRoughAbove z n then 1 else 0) ∧
      cubicSieveUpper z m n - (if MarkedRoughAbove z n then 1 else 0) ≤ cubicSieveCorrection z m n := by
  have h := BonferroniBlocks.block_bounds (cubicSieveBlockIndices z) (cubicSieveBlock z)
    (cubicSieveOrder m) (fun p => p ∣ n)
  rw [cubicSieveBlock_union, cubicSieve_survives_eq_rough hz,
    BonferroniBlocks.blockLower] at h
  change (cubicSieveUpper z m n - cubicSieveCorrection z m n ≤ _) ∧
    _ ≤ cubicSieveUpper z m n at h
  exact ⟨sub_nonneg.mpr h.2, by linarith [h.1]⟩

end ArtinMatthews
