module

public import ArtinMatthews.CubicSamplingSourceTruncation
public import ArtinMatthews.MarkedBonferroniTail
public import ArtinMatthews.CubicSamplingArraySquareMean
public import ArtinMatthews.CubicSamplingTailEnvelope
public import ArtinMatthews.MarkedArrayBandStructure
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

/-! Actual Section 6.3 square-mean truncation with the literal logarithmic
floor and the original marking-band normalizers. -/

noncomputable section
namespace ArtinMatthews

open Filter
open scoped BigOperators Topology

theorem cubicSampling_actualArray_factorial_mean_eventually {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ j, 0 < e j ∧ e j ≤ 1 / 5) (hinj : Function.Injective e)
    (a : J → ℕ) (ha : ∀ j, 0 < a j) :
    ∃ C T : ℝ, 0 < C ∧ 0 ≤ T ∧ ∀ᶠ x : ℝ in atTop,
      let P := fun j => markedLogPowerBand (e j) x
      let V := fun j => bandReciprocalMass (P j)
      let h := cubicSamplingTruncationDepth x + 1
      (∑ u ∈ Finset.Icc 1 ⌊2 * x⌋₊, (cubicSamplingArrayTail P V a h u) ^ 2) ≤
        C * x * markedFactorialTail T h := by
  let K := ∑ j, a j
  let W : ℝ := Fintype.card J
  let B := max 1 (4 * W)
  let v := Real.log 2 / 2
  let Cb := (1 / v) ^ K
  let Cg := ((2 * K + 3 : ℕ) : ℝ) ^ (2 * K + 1) * B ^ (2 * K)
  let C := 2 * Cb ^ 2 * Cg
  let T := (2 : ℝ) ^ (2 * K + 1) * B ^ 2
  have hW : 0 ≤ W := Nat.cast_nonneg _
  have hv : 0 < v := by dsimp only [v]; positivity
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hCb : 0 < Cb := by dsimp only [Cb]; positivity
  have hCg : 0 < Cg := by dsimp only [Cg]; positivity
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  refine ⟨C, T, by dsimp only [C]; positivity, hT, ?_⟩
  have hb := marked_actual_band_structure_eventually e (fun j => (he j).1) hinj
    (α := 0) (β := 1 / 5) (fun j => (he j).1.le) (fun j => (he j).2)
  filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with x hxBand hx
  obtain ⟨hdis, hP, hV, hmass⟩ := hxBand
  let P := fun j => markedLogPowerBand (e j) x
  let V := fun j => bandReciprocalMass (P j)
  let N := ⌊2 * x⌋₊
  let h := cubicSamplingTruncationDepth x + 1
  let D := 2 * h + 2 * K
  have hh : 0 < h := Nat.succ_pos _
  have hN : (N : ℝ) ≤ 2 * x := Nat.floor_le (by positivity)
  have hf := cubicSampling_arrayTail_factorial_mean P V a ha hv hV
    (fun j p hp => (hP j p hp).1) hdis hW hmass N h hh
  have henv := cubicSampling_tail_factorial_envelope K h hh hB.le
  have hnTail := markedFactorialTail_nonneg hT h
  calc
    _ ≤ Cb ^ 2 * (N : ℝ) *
        (((D + 1 : ℕ) : ℝ) * (D : ℝ) ^ (2 * K) * B ^ D / (h.factorial : ℝ)) := by
      simpa only [Cb, K, B, D, mul_assoc, div_eq_mul_inv] using hf
    _ ≤ Cb ^ 2 * (N : ℝ) * (Cg * markedFactorialTail T h) :=
      mul_le_mul_of_nonneg_left henv (by positivity)
    _ ≤ Cb ^ 2 * (2 * x) * (Cg * markedFactorialTail T h) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN (sq_nonneg Cb))
        (mul_nonneg hCg.le hnTail)
    _ = C * x * markedFactorialTail T h := by dsimp only [C]; ring

theorem cubicSampling_actualArray_squareMean_log_saving {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ j, 0 < e j ∧ e j ≤ 1 / 5) (hinj : Function.Injective e)
    (a : J → ℕ) (ha : ∀ j, 0 < a j) (A : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      let P := fun j => markedLogPowerBand (e j) x
      let V := fun j => bandReciprocalMass (P j)
      let h := cubicSamplingTruncationDepth x + 1
      (∑ u ∈ Finset.Icc 1 ⌊2 * x⌋₊, (cubicSamplingArrayTail P V a h u) ^ 2) ≤
        x * (Real.log x) ^ (-A) := by
  obtain ⟨C, T, _hC, hT, hactual⟩ := cubicSampling_actualArray_factorial_mean_eventually e he hinj a ha
  have hlim := (markedFactorialTail_log_depth_tendsto hT (δ := 1 / 100) (by norm_num) A).const_mul C
  simp only [mul_zero] at hlim
  filter_upwards [hactual, hlim.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)),
    eventually_gt_atTop (1 : ℝ)] with x hx hs hx₁
  let h := cubicSamplingTruncationDepth x + 1
  have hlog := Real.log_pos hx₁
  have hb : (C * markedFactorialTail T h) * (Real.log x) ^ A ≤ 1 := by
    change C * ((Real.log x) ^ A * markedFactorialTail T h) < 1 at hs
    calc
      _ = C * ((Real.log x) ^ A * markedFactorialTail T h) := by ring
      _ ≤ _ := hs.le
  have hbound := (le_div_iff₀ (Real.rpow_pos_of_pos hlog A)).mpr hb
  rw [one_div, ← Real.rpow_neg hlog.le] at hbound
  calc
    _ ≤ C * x * markedFactorialTail T h := hx
    _ = x * (C * markedFactorialTail T h) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (zero_le_one.trans hx₁.le)

end ArtinMatthews
