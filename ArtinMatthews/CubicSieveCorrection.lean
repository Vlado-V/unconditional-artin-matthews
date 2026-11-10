module

public import ArtinMatthews.CubicSieveUpper
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

/-! The literal overflow polynomial in the divisor-weighted error has
disjoint correction supports and the exact source level z^(4h+2). -/

noncomputable section
namespace ArtinMatthews

open OAI.Erdos970.NumberTheoryLean
open scoped BigOperators

def cubicSieveCorrectionCoeff (z : ℝ) (m : ℕ) (T : Finset ℕ) : ℝ :=
  ∑ j ∈ cubicSieveBlockIndices z, DisjointBlockExpansion.correctionCoefficient
    (cubicSieveBlockIndices z) (cubicSieveBlock z) (cubicSieveOrder m) j T

theorem cubicSieve_correctionCoeff_abs_le (z : ℝ) (m : ℕ) (T : Finset ℕ) :
    |cubicSieveCorrectionCoeff z m T| ≤ 1 := by
  let B := cubicSieveBlockIndices z
  let F (j : ℕ) := DisjointBlockExpansion.correctionCoefficient B (cubicSieveBlock z)
    (cubicSieveOrder m) j T
  change |∑ j ∈ B, F j| ≤ 1
  by_cases h : ∃ j ∈ B, F j ≠ 0
  · obtain ⟨j, hj, hF⟩ := h
    rw [Finset.sum_eq_single_of_mem j hj]
    · exact DisjointBlockExpansion.correctionCoefficient_abs_le _ _ _ _ _
    · intro i hi hij
      exact DisjointBlockExpansion.correctionCoefficient_disjoint hj hi hij.symm hF
  · have heq : (∑ j ∈ B, F j) = 0 := Finset.sum_eq_zero fun j hj =>
      not_not.mp (fun hF => h ⟨j, hj, hF⟩)
    rw [heq, abs_zero]
    exact zero_le_one

theorem cubicSieve_correctionCoeff_level {z : ℝ} (hz : 1 < z) {m : ℕ} {T : Finset ℕ}
    (hT : T ⊆ Nat.primesLE ⌊z⌋₊) (hc : cubicSieveCorrectionCoeff z m T ≠ 0) :
    0 < roughSubsetDivisor T ∧ Squarefree (roughSubsetDivisor T) ∧
      (roughSubsetDivisor T : ℝ) ≤ z ^ (8 * (m : ℝ) + 2) := by
  let B := cubicSieveBlockIndices z
  let F (j : ℕ) := DisjointBlockExpansion.correctionCoefficient B (cubicSieveBlock z)
    (cubicSieveOrder m) j T
  have hactive : ∃ j ∈ B, F j ≠ 0 := by
    by_contra h
    apply hc
    exact Finset.sum_eq_zero fun j hj => not_not.mp (fun hF => h ⟨j, hj, hF⟩)
  obtain ⟨i, hi, hF⟩ := hactive
  have hp (p : ℕ) (hp : p ∈ T) : p.Prime := (Nat.mem_primesLE.mp (hT hp)).2
  refine ⟨roughSubsetDivisor_pos T hp, roughSubsetDivisor_squarefree T hp, ?_⟩
  have hb (j : ℕ) (hj : j ∈ B) :
      (T ∩ cubicSieveBlock z j).card ≤ 2 * m * (j + 1) + 1 := by
    have hs : (T ∩ cubicSieveBlock z j).card ≤ 2 * cubicSieveOrder m j + 1 := by
      by_cases he : j = i
      · subst j
        exact (DisjointBlockExpansion.correctionCoefficient_own_card hi hF).le
      · exact (DisjointBlockExpansion.correctionCoefficient_other_card hj he hF).trans
          (Nat.le_succ _)
    simpa only [cubicSieveOrder, Nat.mul_comm (j + 1) m, Nat.mul_assoc] using hs
  simpa only [roughSubsetDivisor, Nat.cast_one, mul_one] using
    cubicSieve_block_product_level hz hT m 1 hb

theorem cubicSieve_correction_eq_divisor_sum (z : ℝ) (m n : ℕ) :
    cubicSieveCorrection z m n =
      ∑ T ∈ (Nat.primesLE ⌊z⌋₊).powerset,
        if roughSubsetDivisor T ∣ n then cubicSieveCorrectionCoeff z m T else 0 := by
  let B := cubicSieveBlockIndices z
  let L := cubicSieveBlock z
  let h := cubicSieveOrder m
  let P := Nat.primesLE ⌊z⌋₊
  let F (j : ℕ) (T : Finset ℕ) := DisjointBlockExpansion.correctionCoefficient B L h j T
  let hit (p : ℕ) := p ∣ n
  have hdis : (B : Set ℕ).Pairwise fun i j => Disjoint (L i) (L j) :=
    fun i _ j _ hij => cubicSieveBlock_disjoint z hij
  have hEval (j : ℕ) (hj : j ∈ B) :
      (∑ T ∈ P.powerset, F j T * BonferroniBlocks.intersectionValue T hit) =
        (BonferroniBlocks.coefficientPolynomial (2 * h j) (L j) hit -
          BonferroniBlocks.coefficientPolynomial (2 * h j + 1) (L j) hit) *
          ∏ i ∈ B.erase j, BonferroniBlocks.coefficientPolynomial (2 * h i) (L i) hit := by
    have hh := DisjointBlockExpansion.correctionCoefficient_evaluation B L hdis h hit j hj
    have hUnion : B.biUnion L = P := cubicSieveBlock_union z
    rw [hUnion] at hh
    exact hh
  unfold cubicSieveCorrection
  calc
    _ = ∑ j ∈ B, ∑ T ∈ P.powerset, F j T * BonferroniBlocks.intersectionValue T hit := by
      unfold BonferroniBlocks.blockCorrection
      exact Finset.sum_congr rfl (fun j hj => (hEval j hj).symm)
    _ = ∑ T ∈ P.powerset, ∑ j ∈ B, F j T * BonferroniBlocks.intersectionValue T hit :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro T hT
      have hp (p : ℕ) (hp : p ∈ T) : p.Prime :=
        (Nat.mem_primesLE.mp (Finset.mem_powerset.mp hT hp)).2
      change (∑ j ∈ B, F j T * BonferroniBlocks.intersectionValue T (fun p => p ∣ n)) = _
      rw [← Finset.sum_mul, cubicSieve_intersection_eq_divisor T n hp]
      split_ifs
      · simp only [mul_one, cubicSieveCorrectionCoeff, F, B, L, h]
      · rw [mul_zero]

theorem cubicSieve_correction_le_divisors (z : ℝ) (m n : ℕ) (hn : n ≠ 0) :
    cubicSieveCorrection z m n ≤ (n.divisors.card : ℝ) := by
  let P := Nat.primesLE ⌊z⌋₊
  let S := P.powerset.filter (fun T => roughSubsetDivisor T ∣ n)
  have hp (p : ℕ) (hp : p ∈ P) : p.Prime := (Nat.mem_primesLE.mp hp).2
  have hcard : S.card ≤ n.divisors.card := by
    apply Finset.card_le_card_of_injOn roughSubsetDivisor
    · intro T hT
      exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hT).2, hn⟩
    · exact (DisjointBlockExpansion.prime_product_injective P hp).mono
        (fun T hT => (Finset.mem_filter.mp hT).1)
  rw [cubicSieve_correction_eq_divisor_sum, ← Finset.sum_filter]
  calc
    _ ≤ ∑ _T ∈ S, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro T _hT
      exact (le_abs_self _).trans (cubicSieve_correctionCoeff_abs_le z m T)
    _ = (S.card : ℝ) := by simp
    _ ≤ _ := Nat.cast_le.mpr hcard

end ArtinMatthews
