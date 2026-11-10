module

public import ArtinMatthews.CubicSamplingBaselineCRT
public import ArtinMatthews.CubicSamplingDivisorFourth
public import ArtinMatthews.GiantSamplingLargeSquareWeight
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! The discarded marking layer is charged by the true divisor-fourth
moment. The factor from summing over the shifted moduli is a divisor
count, independently of the modulus cutoff. -/

noncomputable section
namespace ArtinMatthews

open OAI OAI.SevenEighths
open scoped BigOperators

theorem giantCubicSampling_baseline_error_square_le (η : HeckeFamily.Character) {M : ℕ}
    (χ : DirichletCharacter ℂ M) (H H₀ : ℕ → ℂ) (E : ℕ → ℝ)
    (Φ : ℝ → ℝ) (hΦ : ∀ t, ‖Φ t‖ ≤ 1) (x : ℝ) (R : ℕ)
    (hE : ∀ u ∈ Finset.Icc 1 ⌊2 * x⌋₊, ‖H u - H₀ u‖ ≤ E u) :
    (∑ r ∈ Finset.Icc 1 R,
      ‖giantCubicSamplingBaselineSum η χ H Φ x r -
        giantCubicSamplingBaselineSum η χ H₀ Φ x r‖) ^ 2 ≤
      (∑ u ∈ Finset.Icc 1 ⌊2 * x⌋₊, (E u) ^ 2) *
        (∑ u ∈ Finset.Icc 1 ⌊2 * x⌋₊, ((u + 1).divisors.card : ℝ) ^ 4) := by
  let U := Finset.Icc 1 ⌊2 * x⌋₊
  let Q := Finset.Icc 1 R
  let F (r u : ℕ) := (H u - H₀ u) * giantCubicSamplingKernel η χ Φ x r u
  have hsplit (r : ℕ) : giantCubicSamplingBaselineSum η χ H Φ x r -
      giantCubicSamplingBaselineSum η χ H₀ Φ x r = ∑ u ∈ U, F r u := by
    simp only [giantCubicSamplingBaselineSum, ← Finset.sum_sub_distrib, ← sub_mul, F, U]
  simp_rw [hsplit]
  have htotal : (∑ r ∈ Q, ‖∑ u ∈ U, F r u‖) ≤
      ∑ u ∈ U, E u * ((u + 1).divisors.card : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ r ∈ Q, ∑ u ∈ U, ‖F r u‖ := Finset.sum_le_sum (fun r _ => norm_sum_le _ _)
      _ = ∑ u ∈ U, ∑ r ∈ Q, ‖F r u‖ := Finset.sum_comm
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro u hu
        exact giantCubicSampling_sum_moduli_norm_le η χ Φ x R u (H u - H₀ u)
          ((norm_nonneg _).trans (hE u hu)) (hE u hu) (hΦ _)
  calc
    _ ≤ (∑ u ∈ U, E u * ((u + 1).divisors.card : ℝ) ^ 2) ^ 2 :=
      pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) htotal 2
    _ ≤ _ := by
      have hpow (u : ℕ) : (((u + 1).divisors.card : ℝ) ^ 2) ^ 2 =
          ((u + 1).divisors.card : ℝ) ^ 4 := by rw [← pow_mul]
      have hsum : (∑ u ∈ U, (((u + 1).divisors.card : ℝ) ^ 2) ^ 2) =
          ∑ u ∈ U, ((u + 1).divisors.card : ℝ) ^ 4 :=
        Finset.sum_congr rfl (fun u _ => hpow u)
      have h := Finset.sum_mul_sq_le_sq_mul_sq U E (fun u => ((u + 1).divisors.card : ℝ) ^ 2)
      change _ ≤ (∑ u ∈ U, E u ^ 2) *
        ∑ u ∈ U, (((u + 1).divisors.card : ℝ) ^ 2) ^ 2 at h
      rw [hsum] at h
      exact h

theorem cubicSampling_shifted_divisor_fourth_log_bound {x : ℝ} (hx : 1 ≤ x)
    (hlog : 1 ≤ Real.log x) :
    (∑ u ∈ Finset.Icc 1 ⌊2 * x⌋₊, ((u + 1).divisors.card : ℝ) ^ 4) ≤
      3 * (2 + Real.log 3) ^ 15 * x * (Real.log x) ^ 15 := by
  let N := ⌊2 * x⌋₊
  let n := ((N + 1 : ℕ) : ℝ)
  have hn : n ≤ 3 * x := by
    dsimp only [n]
    push_cast
    linarith [Nat.floor_le (show 0 ≤ 2 * x by positivity)]
  have hn₁ : 1 ≤ n := by
    dsimp only [n]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
  have hlogn := Real.log_le_log (zero_lt_one.trans_le hn₁) hn
  rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (zero_lt_one.trans_le hx).ne'] at hlogn
  have hplus : 1 + Real.log n ≤ (2 + Real.log 3) * Real.log x := by
    nlinarith [mul_le_mul_of_nonneg_left hlog (show 0 ≤ 1 + Real.log 3 by positivity)]
  have hnonneg := add_nonneg zero_le_one (Real.log_nonneg hn₁)
  calc
    _ ≤ n * (1 + Real.log n) ^ 15 := cubicSampling_shifted_divisor_fourth_moment N
    _ ≤ (3 * x) * ((2 + Real.log 3) * Real.log x) ^ 15 :=
      mul_le_mul hn (pow_le_pow_left₀ hnonneg hplus 15) (pow_nonneg hnonneg _) (by positivity)
    _ = _ := by rw [mul_pow]; ring

end ArtinMatthews
