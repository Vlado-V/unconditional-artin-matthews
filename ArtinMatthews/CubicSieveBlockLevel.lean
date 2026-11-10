module

public import ArtinMatthews.CubicSieveTopBlocks
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
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
public import OAI.NumberTheory.Jacobsthal.Estimates.DisjointBlockExpansion


set_option backward.privateInPublic true
@[expose] public section

/-! The actual top-down block heights give the source divisor level.
The retained depths add to 4h in logarithmic scale, with at most two
additional units for one overflow layer. -/

noncomputable section
namespace ArtinMatthews

open OAI.Erdos970.NumberTheoryLean
open scoped BigOperators

private theorem cubicSieve_geom_range (n : ℕ) :
    (∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ j) = 2 - 2 * (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

private theorem cubicSieve_geom_weighted_range (n : ℕ) :
    (∑ j ∈ Finset.range n, ((j + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ j) =
      4 - (2 * (n : ℝ) + 4) * (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    push_cast
    ring

theorem cubicSieve_geometric_level_sums (B : Finset ℕ) :
    (∑ j ∈ B, (1 / 2 : ℝ) ^ j) ≤ 2 ∧
      (∑ j ∈ B, ((j + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ j) ≤ 4 := by
  let N := B.sup id + 1
  have hsub : B ⊆ Finset.range N := fun j hj =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hj))
  constructor
  · calc
      _ ≤ ∑ j ∈ Finset.range N, (1 / 2 : ℝ) ^ j :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = _ := cubicSieve_geom_range N
      _ ≤ _ := sub_le_self _ (by positivity)
  · calc
      _ ≤ ∑ j ∈ Finset.range N, ((j + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ j :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = _ := cubicSieve_geom_weighted_range N
      _ ≤ _ := sub_le_self _ (by positivity)

theorem cubicSieve_block_product_level {z : ℝ} (hz : 1 < z) {T : Finset ℕ}
    (hT : T ⊆ Nat.primesLE ⌊z⌋₊) (m extra : ℕ)
    (hcard : ∀ j ∈ cubicSieveBlockIndices z,
      (T ∩ cubicSieveBlock z j).card ≤ 2 * m * (j + 1) + extra) :
    ((∏ p ∈ T, p : ℕ) : ℝ) ≤ z ^ (8 * (m : ℝ) + 2 * (extra : ℝ)) := by
  let B := cubicSieveBlockIndices z
  let L (j : ℕ) := cubicSieveBlock z j
  let k (j : ℕ) := 2 * m * (j + 1) + extra
  let q (j : ℕ) := (1 / 2 : ℝ) ^ j
  have hdis : (B : Set ℕ).Pairwise fun i j => Disjoint (L i) (L j) :=
    fun i _ j _ hij => cubicSieveBlock_disjoint z hij
  have hUnion : T ⊆ B.biUnion L := by
    change T ⊆ (cubicSieveBlockIndices z).biUnion (cubicSieveBlock z)
    rw [cubicSieveBlock_union]
    exact hT
  have hexp : (∑ j ∈ B, q j * (k j : ℝ)) ≤ 8 * (m : ℝ) + 2 * (extra : ℝ) := by
    obtain ⟨h₁, h₂⟩ := cubicSieve_geometric_level_sums B
    calc
      _ = (2 * (m : ℝ)) * (∑ j ∈ B, ((j + 1 : ℕ) : ℝ) * q j) +
          (extra : ℝ) * (∑ j ∈ B, q j) := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _hj
        dsimp only [k]
        push_cast
        ring
      _ ≤ (2 * (m : ℝ)) * 4 + (extra : ℝ) * 2 :=
        add_le_add (mul_le_mul_of_nonneg_left h₂ (by positivity))
          (mul_le_mul_of_nonneg_left h₁ (Nat.cast_nonneg _))
      _ = _ := by ring
  rw [Nat.cast_prod, DisjointBlockExpansion.prod_inter_blocks B L hdis hUnion (fun p => (p : ℝ))]
  calc
    _ ≤ ∏ j ∈ B, (z ^ q j) ^ k j := by
      apply Finset.prod_le_prod₀ (fun j _ => Finset.prod_nonneg (fun p _ => Nat.cast_nonneg p))
      intro j hj
      calc
        _ ≤ ∏ _p ∈ T ∩ L j, z ^ q j := Finset.prod_le_prod₀ (fun p _ => Nat.cast_nonneg p)
          (fun p hp => ((mem_cubicSieveBlock hz).mp (Finset.mem_inter.mp hp).2).2.2)
        _ = (z ^ q j) ^ (T ∩ L j).card := Finset.prod_const _
        _ ≤ _ := pow_le_pow_right₀ (Real.one_le_rpow hz.le (by dsimp only [q]; positivity)) (hcard j hj)
    _ = z ^ (∑ j ∈ B, q j * (k j : ℝ)) := by
      rw [Real.rpow_sum_of_pos (zero_lt_one.trans hz)]
      apply Finset.prod_congr rfl
      intro j _hj
      exact (Real.rpow_mul_natCast (zero_le_one.trans hz.le) (q j) (k j)).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hz.le hexp

end ArtinMatthews
