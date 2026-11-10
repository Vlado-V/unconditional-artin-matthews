module

public import ArtinMatthews.CubicSamplingSourceTruncation
public import ArtinMatthews.CubicSieveUpper
public import ArtinMatthews.CubicSamplingBaselineCauchy
public import ArtinMatthews.CubicSamplingSourceTail
public import ArtinMatthews.CubicSieveCorrection
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

/-! The discarded marking layer in (7.11), weighted by the original
divisor function and the actual nonnegative overflow polynomial. -/

noncomputable section
namespace ArtinMatthews

open Finset Filter
open scoped BigOperators Topology

theorem cubicSieve_arrayReplacement_square_le (H H₀ E F : ℕ → ℝ) (x : ℝ)
    (hE : ∀ u ∈ Icc 1 ⌊2 * x⌋₊, |H u - H₀ u| ≤ E u)
    (hF : ∀ u ∈ Icc 1 ⌊2 * x⌋₊, |F u| ≤ ((u + 1).divisors.card : ℝ) ^ 2) :
    |∑ u ∈ Icc 1 ⌊2 * x⌋₊, (H u - H₀ u) * F u| ^ 2 ≤
      (∑ u ∈ Icc 1 ⌊2 * x⌋₊, E u ^ 2) *
        (∑ u ∈ Icc 1 ⌊2 * x⌋₊, ((u + 1).divisors.card : ℝ) ^ 4) := by
  let U := Icc 1 ⌊2 * x⌋₊
  have hsum : |∑ u ∈ U, (H u - H₀ u) * F u| ≤
      ∑ u ∈ U, E u * ((u + 1).divisors.card : ℝ) ^ 2 := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    apply sum_le_sum
    intro u hu
    rw [abs_mul]
    exact mul_le_mul (hE u hu) (hF u hu) (abs_nonneg _) ((abs_nonneg _).trans (hE u hu))
  calc
    _ ≤ (∑ u ∈ U, E u * ((u + 1).divisors.card : ℝ) ^ 2) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) hsum 2
    _ ≤ _ := by
      have h := sum_mul_sq_le_sq_mul_sq U E (fun u => ((u + 1).divisors.card : ℝ) ^ 2)
      simpa only [← pow_mul] using h

theorem cubicSieve_arrayReplacement_log_saving {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ j, 0 < e j ∧ e j ≤ 1 / 5) (hinj : Function.Injective e)
    (a : J → ℕ) (ha : ∀ j, 0 < a j) (A : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      let P := fun j => markedLogPowerBand (e j) x
      let V := fun j => bandReciprocalMass (P j)
      let k := cubicSamplingTruncationDepth x
      ∀ F : ℕ → ℝ, (∀ u ∈ Icc 1 ⌊2 * x⌋₊, |F u| ≤ ((u + 1).divisors.card : ℝ) ^ 2) →
        |∑ u ∈ Icc 1 ⌊2 * x⌋₊,
          ((∏ j, (bandWeight (P j) (V j) u) ^ a j) - cubicSamplingArrayTruncation P V a k u) * F u| ≤
          x * (Real.log x) ^ (-A) := by
  let C := 3 * (2 + Real.log 3) ^ 15
  have htr := cubicSampling_actualArray_retained_eventually e he hinj a ha zero_lt_one
  have htail := cubicSampling_actualArray_squareMean_log_saving e he hinj a ha (2 * A + 16)
  have hlog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 C))
  filter_upwards [htr, htail, hlog, eventually_gt_atTop (1 : ℝ)] with x hxtr hxtail hxl hx₁
  dsimp only
  intro F hF
  let P := fun j => markedLogPowerBand (e j) x
  let V := fun j => bandReciprocalMass (P j)
  let k := cubicSamplingTruncationDepth x
  let L := Real.log x
  let U := Icc 1 ⌊2 * x⌋₊
  let H (u : ℕ) := ∏ j, (bandWeight (P j) (V j) u) ^ a j
  let H₀ (u : ℕ) := cubicSamplingArrayTruncation P V a k u
  let E := cubicSamplingArrayTail P V a (k + 1)
  have hL : 0 < L := Real.log_pos hx₁
  have hL₁ : 1 ≤ L := (le_max_left _ _).trans hxl
  have hLC : C ≤ L := (le_max_right _ _).trans hxl
  have hE (u : ℕ) (_hu : u ∈ U) : |H u - H₀ u| ≤ E u := hxtr.1 u
  have hp : L ^ (-(2 * A + 16)) * L ^ (15 : ℕ) = L ^ (-A) * L ^ (-A) * L⁻¹ := by
    calc
      _ = L ^ (-(2 * A + 16) + 15) := by
        rw [Real.rpow_add hL, show L ^ (15 : ℝ) = L ^ (15 : ℕ) from Real.rpow_natCast L 15]
      _ = L ^ ((-A) + (-A) + (-1)) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hL, Real.rpow_add hL, Real.rpow_neg_one]
  have hSq : |∑ u ∈ U, (H u - H₀ u) * F u| ^ 2 ≤ (x * L ^ (-A)) ^ 2 := by
    calc
      _ ≤ (∑ u ∈ U, E u ^ 2) * (∑ u ∈ U, ((u + 1).divisors.card : ℝ) ^ 4) :=
        cubicSieve_arrayReplacement_square_le H H₀ E F x hE hF
      _ ≤ (x * L ^ (-(2 * A + 16))) * (C * x * L ^ (15 : ℕ)) :=
        mul_le_mul hxtail (cubicSampling_shifted_divisor_fourth_log_bound hx₁.le hL₁)
          (sum_nonneg (fun _ _ => by positivity)) (by positivity)
      _ = (x * L ^ (-A)) ^ 2 * (C / L) := by
        calc
          _ = C * x ^ 2 * (L ^ (-(2 * A + 16)) * L ^ (15 : ℕ)) := by ring
          _ = _ := by rw [hp]; ring
      _ ≤ _ := mul_le_of_le_one_right (sq_nonneg _) ((div_le_one hL).mpr hLC)
  exact (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ x * L ^ (-A))).mp hSq

theorem cubicSieve_overflow_arrayReplacement_log_saving {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ j, 0 < e j ∧ e j ≤ 1 / 5) (hinj : Function.Injective e)
    (a : J → ℕ) (ha : ∀ j, 0 < a j) (Φ : ℝ → ℝ) (hΦ : ∀ t, |Φ t| ≤ 1) (A : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      let P := fun j => markedLogPowerBand (e j) x
      let V := fun j => bandReciprocalMass (P j)
      let k := cubicSamplingTruncationDepth x
      ∀ z : ℝ, 0 ≤ z → ∀ m : ℕ,
        |∑ u ∈ Icc 1 ⌊2 * x⌋₊, Φ ((u : ℝ) / x) *
          ((∏ j, (bandWeight (P j) (V j) u) ^ a j) - cubicSamplingArrayTruncation P V a k u) *
          ((u + 1).divisors.card : ℝ) * cubicSieveCorrection z m (u + 1)| ≤
            x * (Real.log x) ^ (-A) := by
  filter_upwards [cubicSieve_arrayReplacement_log_saving e he hinj a ha A] with x hx
  dsimp only at hx ⊢
  intro z hz m
  have hF (u : ℕ) (_hu : u ∈ Icc 1 ⌊2 * x⌋₊) :
      |Φ ((u : ℝ) / x) * ((u + 1).divisors.card : ℝ) * cubicSieveCorrection z m (u + 1)| ≤
        ((u + 1).divisors.card : ℝ) ^ 2 := by
    have hτ : 0 ≤ ((u + 1).divisors.card : ℝ) := Nat.cast_nonneg _
    have hc := cubicSieve_correction_le_divisors z m (u + 1) (by omega)
    have hc₀ : 0 ≤ cubicSieveCorrection z m (u + 1) :=
      (cubicSieve_upper_rough_error hz m (u + 1)).1.trans (cubicSieve_upper_rough_error hz m (u + 1)).2
    rw [abs_mul, abs_mul, abs_of_nonneg hτ, abs_of_nonneg hc₀]
    exact (mul_le_mul (mul_le_mul_of_nonneg_right (hΦ _) hτ) hc hc₀ (by positivity)).trans_eq (by ring)
  have h := hx (fun u => Φ ((u : ℝ) / x) * ((u + 1).divisors.card : ℝ) *
    cubicSieveCorrection z m (u + 1)) hF
  convert h using 2
  apply sum_congr rfl
  intro u _
  ring

end ArtinMatthews
