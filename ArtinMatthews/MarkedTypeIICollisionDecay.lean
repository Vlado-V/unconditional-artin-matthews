module

public import ArtinMatthews.ReciprocalTail
public import ArtinMatthews.MarkedEstimateMertensBandCore
public import ArtinMatthews.MarkedBonferroniTail


set_option backward.privateInPublic true
@[expose] public section

/-!
# Reciprocal-square suppression for marked-label collisions

The discarded squareful labels and common-prime labels in PD §3.1 and §4.9
are controlled by the sum of reciprocal squares of marking primes. This file
proves that sum is exponentially small in `(log x)^(1/10)`, uniformly over the
band exponents. The proof uses the actual finite prime bands and a telescoping
integer tail; no prime-number estimate or collision bound is assumed.
-/

namespace ArtinMatthews

open Filter
open scoped BigOperators Topology

/-- Every finite set of integers above `y ≥ 4` has reciprocal-square mass at
most `4/y`. In particular this applies to any union of marking bands. -/
theorem marked_reciprocal_square_tail_le (P : Finset ℕ) {y : ℝ} (hy : 4 ≤ y)
    (hP : ∀ p ∈ P, y ≤ (p : ℝ)) :
    (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ≤ 4 / y := by
  let Y : ℕ := ⌊y / 2⌋₊
  have hy0 : 0 < y := by linarith
  have hY : 0 < Y := by
    apply Nat.lt_of_lt_of_le (by norm_num : 0 < 1)
    apply Nat.le_floor
    linarith
  have hYle : (Y : ℝ) ≤ y / 2 := Nat.floor_le (by linarith)
  have hYge : y / 4 ≤ (Y : ℝ) := by
    have hf := Nat.sub_one_lt_floor (y / 2)
    change y / 2 - 1 < (Y : ℝ) at hf
    linarith
  have hPY : ∀ p ∈ P, Y < p := by
    intro p hp
    have := hP p hp
    exact_mod_cast (show (Y : ℝ) < p by linarith)
  calc
    (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ≤
        ∑ p ∈ P, 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hp4 := hP p hp
      have hp0 : (0 : ℝ) < p := by linarith
      have hp1 : (1 : ℝ) < p := by linarith
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    _ ≤ 1 / (Y : ℝ) := sum_reciprocal_tail_le P Y hY hPY
    _ ≤ 4 / y := by
      apply (div_le_div_iff₀ (by exact_mod_cast hY) hy0).mpr
      nlinarith

/-- All actual marking primes lie above the same exponential threshold when
the band exponent is at least `1/10` and `log x ≥ 1`. -/
theorem marked_band_common_lower {a x : ℝ} (ha : (1 / 10 : ℝ) ≤ a)
    (hx : 1 ≤ Real.log x) {p : ℕ} (hp : p ∈ markedLogPowerBand a x) :
    Real.exp ((Real.log x) ^ (1 / 10 : ℝ)) ≤ (p : ℝ) := by
  apply (Real.exp_le_exp.mpr (Real.rpow_le_rpow_of_exponent_le hx ha)).trans
  exact (mem_markedLogPowerBand.mp hp).2.1

/-- The reciprocal-square mass of the complete union of marking bands is
uniformly exponentially small. The constant and threshold do not depend on
the number of bands or their particular exponents. -/
theorem marked_bands_reciprocal_square_le_eventually {ι : Type*}
    (I : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ I, (1 / 10 : ℝ) ≤ a i) :
    ∀ᶠ x : ℝ in atTop,
      (∑ p ∈ I.biUnion (fun i => markedLogPowerBand (a i) x), 1 / (p : ℝ) ^ 2) ≤
        4 * Real.exp (-(Real.log x) ^ (1 / 10 : ℝ)) := by
  classical
  have hgrowth := Real.tendsto_exp_atTop.comp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp Real.tendsto_log_atTop)
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    hgrowth.eventually (eventually_ge_atTop (4 : ℝ))] with x hx hgrowth
  have hbound := marked_reciprocal_square_tail_le
    (I.biUnion (fun i => markedLogPowerBand (a i) x)) hgrowth (by
      intro p hp
      obtain ⟨i, hi, hp⟩ := Finset.mem_biUnion.mp hp
      exact marked_band_common_lower (ha i hi) hx hp)
  simpa only [Function.comp_def, div_eq_mul_inv, Real.exp_neg] using hbound

/-- The actual collision kernel saves every fixed logarithmic power. -/
theorem marked_bands_reciprocal_square_log_saving {ι : Type*}
    (I : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ I, (1 / 10 : ℝ) ≤ a i) (A : ℝ) :
    Tendsto (fun x : ℝ => (Real.log x) ^ A *
      ∑ p ∈ I.biUnion (fun i => markedLogPowerBand (a i) x), 1 / (p : ℝ) ^ 2)
      atTop (nhds 0) := by
  classical
  have hdecay := ((rpow_mul_exp_neg_rpow_tendsto A
    (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 1)).comp
      Real.tendsto_log_atTop).const_mul 4
  simp only [Function.comp_def, neg_mul, one_mul, mul_zero] at hdecay
  apply squeeze_zero' _ _ hdecay
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact mul_nonneg (Real.rpow_nonneg (Real.log_nonneg hx) A)
      (Finset.sum_nonneg (fun _ _ => by positivity))
  · filter_upwards [marked_bands_reciprocal_square_le_eventually I a ha,
      eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have h := mul_le_mul_of_nonneg_left hx (Real.rpow_nonneg (Real.log_nonneg hx1) A)
    convert h using 1
    ring

end ArtinMatthews
