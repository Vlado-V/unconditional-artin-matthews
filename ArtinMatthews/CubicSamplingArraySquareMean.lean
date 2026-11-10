module

public import ArtinMatthews.CubicSamplingArrayTruncation
public import ArtinMatthews.CubicSamplingChooseMoment
public import ArtinMatthews.CubicSamplingTailPointwise
public import ArtinMatthews.CubicSamplingTailUnion
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
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

/-! Square-mean estimate for the actual normalized represented array
tail. Positive multiples over [1,N] have a floor bound, so the overlap
calculation introduces no rounding loss. -/

noncomputable section
namespace ArtinMatthews

open scoped BigOperators

theorem cubicSampling_arrayTail_squareMean {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (V : J → ℝ) (a : J → ℕ) (ha : ∀ j, 0 < a j)
    {v W : ℝ} (hv : 0 < v) (hV : ∀ j, v ≤ V j)
    (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise fun i j => Disjoint (P i) (P j))
    (hW : 0 ≤ W) (hmass : ∑ p ∈ Finset.univ.biUnion P, 1 / (p : ℝ) ≤ W)
    (N h : ℕ) (hh : 0 < h) :
    (∑ u ∈ Finset.Icc 1 N, (cubicSamplingArrayTail P V a h u) ^ 2) ≤
      ((1 / v) ^ (∑ j, a j)) ^ 2 * (N : ℝ) *
        (∑ k ∈ Finset.Icc h (2 * h + 2 * (∑ j, a j)),
          (k : ℝ) ^ (2 * (∑ j, a j)) * (4 * W) ^ k / (k.factorial : ℝ)) := by
  let U := Finset.univ.biUnion P
  let K := ∑ j, a j
  let C := (1 / v) ^ K
  let D := Finset.Icc h (2 * h + 2 * K)
  let n (u : ℕ) := bandCount U u
  have hU (p : ℕ) (hp : p ∈ U) : p.Prime := by
    obtain ⟨j, _hj, hpj⟩ := Finset.mem_biUnion.mp hp
    exact hP j p hpj
  have hE (u : ℕ) : 0 ≤ cubicSamplingArrayTail P V a h u := by
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, h = k + 1 := ⟨h - 1, by omega⟩
    exact (abs_nonneg _).trans
      (cubicSampling_arrayTruncation_error P V a ha (fun j => hv.le.trans (hV j)) hP hdis k u)
  have hp (u : ℕ) :
      (cubicSamplingArrayTail P V a h u) ^ 2 ≤
        C ^ 2 * ∑ k ∈ D, (k : ℝ) ^ (2 * K) * (4 : ℝ) ^ k * ((n u).choose k : ℝ) := by
    have hchoose : (n u : ℝ) ^ (2 * K) * ((n u).choose h : ℝ) ^ 2 ≤
        ∑ k ∈ D, (k : ℝ) ^ (2 * K) * (4 : ℝ) ^ k * ((n u).choose k : ℝ) := by
      exact_mod_cast cubicSampling_tail_union_count (activeDivisors U u) (2 * K) h
    calc
      _ ≤ (C * (n u : ℝ) ^ K * ((n u).choose h : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (hE u) (cubicSampling_arrayTail_le_binomial P V a hv hV hP hdis h u) 2
      _ = C ^ 2 * ((n u : ℝ) ^ (2 * K) * ((n u).choose h : ℝ) ^ 2) := by
        rw [mul_pow, mul_pow, ← pow_mul, Nat.mul_comm K 2]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hchoose (sq_nonneg C)
  calc
    _ ≤ ∑ u ∈ Finset.Icc 1 N,
        C ^ 2 * ∑ k ∈ D, (k : ℝ) ^ (2 * K) * (4 : ℝ) ^ k * ((n u).choose k : ℝ) :=
      Finset.sum_le_sum (fun u _ => hp u)
    _ = C ^ 2 * (∑ k ∈ D, (k : ℝ) ^ (2 * K) * (4 : ℝ) ^ k *
        ∑ u ∈ Finset.Icc 1 N, ((n u).choose k : ℝ)) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp_rw [Finset.mul_sum]
    _ ≤ C ^ 2 * (∑ k ∈ D, (k : ℝ) ^ (2 * K) * (4 : ℝ) ^ k *
        ((N : ℝ) * (W ^ k / (k.factorial : ℝ)))) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg C)
      apply Finset.sum_le_sum
      intro k _hk
      exact mul_le_mul_of_nonneg_left
        (cubicSampling_binomial_hit_moment U hU N k hW hmass) (by positivity)
    _ = _ := by
      change _ = C ^ 2 * (N : ℝ) *
        ∑ k ∈ D, (k : ℝ) ^ (2 * K) * (4 * W) ^ k / (k.factorial : ℝ)
      have hfactor : (∑ k ∈ D, (k : ℝ) ^ (2 * K) * (4 : ℝ) ^ k *
          ((N : ℝ) * (W ^ k / (k.factorial : ℝ)))) =
          (N : ℝ) * ∑ k ∈ D, (k : ℝ) ^ (2 * K) * (4 * W) ^ k / (k.factorial : ℝ) := by
        rw [Finset.mul_sum D
          (fun k => (k : ℝ) ^ (2 * K) * (4 * W) ^ k / (k.factorial : ℝ)) (N : ℝ)]
        apply Finset.sum_congr rfl
        intro k _hk
        rw [mul_pow]
        ring
      rw [hfactor, mul_assoc]

theorem cubicSampling_arrayTail_factorial_mean {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (V : J → ℝ) (a : J → ℕ) (ha : ∀ j, 0 < a j)
    {v W : ℝ} (hv : 0 < v) (hV : ∀ j, v ≤ V j)
    (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise fun i j => Disjoint (P i) (P j))
    (hW : 0 ≤ W) (hmass : ∑ p ∈ Finset.univ.biUnion P, 1 / (p : ℝ) ≤ W)
    (N h : ℕ) (hh : 0 < h) :
    let K := ∑ j, a j
    let D := 2 * h + 2 * K
    (∑ u ∈ Finset.Icc 1 N, (cubicSamplingArrayTail P V a h u) ^ 2) ≤
      ((1 / v) ^ K) ^ 2 * (N : ℝ) *
        ((D + 1 : ℕ) : ℝ) * (D : ℝ) ^ (2 * K) * (max 1 (4 * W)) ^ D / (h.factorial : ℝ) := by
  dsimp only
  let K := ∑ j, a j
  let D := 2 * h + 2 * K
  let S := Finset.Icc h D
  let B := max 1 (4 * W)
  let C := (1 / v) ^ K
  have hsum : (∑ k ∈ S, (k : ℝ) ^ (2 * K) * (4 * W) ^ k / (k.factorial : ℝ)) ≤
      ((D + 1 : ℕ) : ℝ) * ((D : ℝ) ^ (2 * K) * B ^ D / (h.factorial : ℝ)) := by
    have hcard : S.card ≤ D + 1 := by
      have hsub : S ⊆ Finset.range (D + 1) := fun k hk =>
        Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hk).2)
      simpa only [Finset.card_range] using Finset.card_le_card hsub
    calc
      _ ≤ ∑ _k ∈ S, (D : ℝ) ^ (2 * K) * B ^ D / (h.factorial : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hk
        have hpow : (4 * W) ^ k ≤ B ^ D := (pow_le_pow_left₀ (by positivity) (le_max_right _ _) k).trans
          (pow_le_pow_right₀ (le_max_left _ _) hhi)
        apply div_le_div₀ (by positivity) _ (by positivity) (by exact_mod_cast Nat.factorial_le hlo)
        exact mul_le_mul
          (pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr hhi) (2 * K)) hpow
          (by positivity) (by positivity)
      _ = (S.card : ℝ) * ((D : ℝ) ^ (2 * K) * B ^ D / (h.factorial : ℝ)) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) (by dsimp only [B]; positivity)
  calc
    _ ≤ C ^ 2 * (N : ℝ) * ∑ k ∈ S, (k : ℝ) ^ (2 * K) * (4 * W) ^ k / (k.factorial : ℝ) :=
      cubicSampling_arrayTail_squareMean P V a ha hv hV hP hdis hW hmass N h hh
    _ ≤ C ^ 2 * (N : ℝ) * (((D + 1 : ℕ) : ℝ) *
        ((D : ℝ) ^ (2 * K) * B ^ D / (h.factorial : ℝ))) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

end ArtinMatthews
