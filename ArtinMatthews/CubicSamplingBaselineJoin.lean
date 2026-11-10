module

public import ArtinMatthews.CubicSamplingBaselineCRT
public import ArtinMatthews.CubicSamplingBaselineActualError
public import ArtinMatthews.CubicSamplingBaselineRetained
public import ArtinMatthews.HeckePrimeLogSaving
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The retained norm classes and the actual discarded marking layer
together give the full Section 6.2–6.3 baseline bound. -/

noncomputable section
namespace ArtinMatthews

open Filter OAI OAI.SevenEighths
open scoped BigOperators ContDiff Topology

private theorem cubicSampling_retained_budget_power_le {C x ε : ℝ}
    (hC : 0 ≤ C) (hx : 1 ≤ x) (hε : ε < 1 / 4) :
    let R := (⌊x ^ (ε / 64)⌋₊ : ℝ)
    let D := x ^ (1 / 32 : ℝ)
    C * (R * D) * (R * D * Real.sqrt x + (R * D) ^ 2) ≤
      (2 * C) * x ^ (3 / 4 : ℝ) := by
  dsimp only
  let R := (⌊x ^ (ε / 64)⌋₊ : ℝ)
  let D := x ^ (1 / 32 : ℝ)
  have hx₀ := zero_lt_one.trans_le hx
  have hD : 0 ≤ D := Real.rpow_nonneg hx₀.le _
  have hR : R ≤ D :=
    (Nat.floor_le (Real.rpow_nonneg hx₀.le (ε / 64))).trans
      (Real.rpow_le_rpow_of_exponent_le hx (by linarith))
  have hRD : R * D ≤ D ^ 2 := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right hR hD
  have hRD₀ : 0 ≤ R * D := by positivity
  have h4 : D ^ 4 * Real.sqrt x = x ^ (5 / 8 : ℝ) := by
    dsimp only [D]
    rw [← Real.rpow_mul_natCast hx₀.le, Real.sqrt_eq_rpow, ← Real.rpow_add hx₀]
    congr 1
    norm_num
  have h6 : D ^ 6 = x ^ (3 / 16 : ℝ) := by
    dsimp only [D]
    rw [← Real.rpow_mul_natCast hx₀.le]
    congr 1
    norm_num
  calc
    _ ≤ C * D ^ 2 * (D ^ 2 * Real.sqrt x + (D ^ 2) ^ 2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hRD hC)
        (add_le_add (mul_le_mul_of_nonneg_right hRD (Real.sqrt_nonneg _))
          (pow_le_pow_left₀ hRD₀ hRD 2)) (by positivity) (by positivity)
    _ = C * (D ^ 4 * Real.sqrt x + D ^ 6) := by ring
    _ = C * (x ^ (5 / 8 : ℝ) + x ^ (3 / 16 : ℝ)) := by rw [h4, h6]
    _ ≤ C * (x ^ (3 / 4 : ℝ) + x ^ (3 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (Real.rpow_le_rpow_of_exponent_le hx (by norm_num))
          (Real.rpow_le_rpow_of_exponent_le hx (by norm_num))) hC
    _ = _ := by ring

theorem cubicSampling_two_log_errors {x : ℝ} (hx : 0 ≤ x) (hlog : 2 ≤ Real.log x) (G : ℝ) :
    x * (Real.log x) ^ (-(G + 1)) + x * (Real.log x) ^ (-(G + 1)) ≤
      x * (Real.log x) ^ (-G) := by
  let L := Real.log x
  have hL : 0 < L := lt_of_lt_of_le (by norm_num) hlog
  have hp : L ^ (-(G + 1)) = L ^ (-G) / L := by
    rw [show -(G + 1) = -G + (-1) by ring, Real.rpow_add hL, Real.rpow_neg_one, div_eq_mul_inv]
  change x * L ^ (-(G + 1)) + x * L ^ (-(G + 1)) ≤ x * L ^ (-G)
  rw [hp]
  calc
    _ = (x * L ^ (-G)) * (2 / L) := by ring
    _ ≤ _ := mul_le_of_le_one_right (by positivity) ((div_le_one hL).mpr hlog)

theorem giantCubicSampling_actualArray_baseline_log_saving
    {J : Type*} [Fintype J] (e : J → ℝ) (he : ∀ j, 0 < e j ∧ e j ≤ 1 / 5)
    (hinj : Function.Injective e) (a : J → ℕ) (ha : ∀ j, 0 < a j)
    (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y ^ 3 = (A : OAI.CubicFirstMoment.Eisenstein))
    {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) {ε : ℝ} (hε : ε < 1 / 4)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hΦ₁ : ∀ t, ‖Φ t‖ ≤ 1)
    (hs : Function.support Φ ⊆ Set.Ioo 1 2) (G : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      let P := fun j => markedLogPowerBand (e j) x
      let V := fun j => bandReciprocalMass (P j)
      let η := cubicNumeratorHeckeCharacter A hA
      let H (u : ℕ) : ℂ := ((∏ j, (bandWeight (P j) (V j) u) ^ a j : ℝ) : ℂ)
      (∑ r ∈ Finset.Icc 1 ⌊x ^ (ε / 64)⌋₊, ‖giantCubicSamplingBaselineSum η χ H Φ x r‖) ≤
        x * (Real.log x) ^ (-G) := by
  let η := cubicNumeratorHeckeCharacter A hA
  obtain ⟨C, hC, hRet⟩ := giantCubicSampling_actualArray_retained_bound e he hinj a ha
    A hA hnoncube χ Φ hΦ hs (γ := 1 / 32) (by norm_num)
  have hErr := giantCubicSampling_actualArray_baseline_error_log_saving e he hinj a ha
    η χ Φ hΦ₁ (G + 1)
  have hPow := heckePrime_uniform_power_log_saving (2 * C) (3 / 4) 1 (G + 1)
    (by positivity) (by norm_num) zero_lt_one
  have hLog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2 : ℝ))
  filter_upwards [hRet, hErr, hPow, hLog, eventually_ge_atTop (1 : ℝ)] with x hr he' hp hlog hx
  let P := fun j => markedLogPowerBand (e j) x
  let V := fun j => bandReciprocalMass (P j)
  let H (u : ℕ) : ℂ := ((∏ j, (bandWeight (P j) (V j) u) ^ a j : ℝ) : ℂ)
  let H₀ (u : ℕ) : ℂ := (cubicSamplingArrayTruncation P V a (cubicSamplingTruncationDepth x) u : ℂ)
  let R := ⌊x ^ (ε / 64)⌋₊
  let B (H : ℕ → ℂ) (r : ℕ) := giantCubicSamplingBaselineSum η χ H Φ x r
  have hRet' : (∑ r ∈ Finset.Icc 1 R, ‖B H₀ r‖) ≤ x * (Real.log x) ^ (-(G + 1)) :=
    ((hr R).trans (cubicSampling_retained_budget_power_le hC.le hx hε)).trans
      (hp x (by rw [Real.rpow_one]))
  calc
    _ ≤ ∑ r ∈ Finset.Icc 1 R, (‖B H r - B H₀ r‖ + ‖B H₀ r‖) := by
      apply Finset.sum_le_sum
      intro r _hr
      calc
        _ = ‖(B H r - B H₀ r) + B H₀ r‖ := congrArg norm (sub_add_cancel _ _).symm
        _ ≤ _ := norm_add_le _ _
    _ = (∑ r ∈ Finset.Icc 1 R, ‖B H r - B H₀ r‖) +
        ∑ r ∈ Finset.Icc 1 R, ‖B H₀ r‖ := Finset.sum_add_distrib
    _ ≤ x * (Real.log x) ^ (-(G + 1)) + x * (Real.log x) ^ (-(G + 1)) :=
      add_le_add (he' R) hRet'
    _ ≤ _ := cubicSampling_two_log_errors (zero_le_one.trans hx) hlog G

end ArtinMatthews
