module

public import ArtinMatthews.GiantPrimeNormalization
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.Basify
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


set_option backward.privateInPublic true
@[expose] public section

/-!
# Removing the marking primes from the giant-prime statistic

The bounded extension below agrees with `f_x-C_x` on the support `0<n≤2x`.
Unlike the uncapped divisor count it is bounded for all positive integers,
and it retains the exact band-prime invariance required in (2.4).
-/

namespace ArtinMatthews

open Filter

theorem giantPrimeFactors_mul_small {m n : ℕ} {x ε : ℝ}
    (hm : 0 < m) (hn : 0 < n) (hsmall : (m : ℝ) ≤ x ^ (1 - ε)) :
    giantPrimeFactors (m * n) x ε = giantPrimeFactors n x ε := by
  classical
  ext p
  simp only [giantPrimeFactors, Finset.mem_filter, mem_primeFactorsAbove]
  constructor
  · rintro ⟨⟨hp, hpd, _, hpl⟩, hpu⟩
    refine ⟨⟨hp, ?_, hn.ne', hpl⟩, hpu⟩
    rcases hp.dvd_mul.mp hpd with hpm | hpn
    · have hle : (p : ℝ) ≤ m := by exact_mod_cast Nat.le_of_dvd hm hpm
      linarith
    · exact hpn
  · rintro ⟨⟨hp, hpd, _, hpl⟩, hpu⟩
    exact ⟨⟨hp, dvd_mul_of_dvd_right hpd m, (Nat.mul_pos hm hn).ne', hpl⟩, hpu⟩

/-- This also removes repeated powers of every marking prime. -/
theorem giantPrimeFactors_pow_mul_small {m n : ℕ} {x ε : ℝ}
    (hm : 0 < m) (hn : 0 < n) (hsmall : (m : ℝ) ≤ x ^ (1 - ε)) (k : ℕ) :
    giantPrimeFactors (m ^ k * n) x ε = giantPrimeFactors n x ε := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_assoc,
      giantPrimeFactors_mul_small hm (Nat.mul_pos (pow_pos hm k) hn) hsmall, ih]

/-- Every fixed sublinear logarithmic marking band eventually lies below the
giant-prime threshold. The paper's exponents in `(0.1,0.2)` satisfy this. -/
theorem marked_band_below_giant_eventually {a ε : ℝ} (ha : a < 1) (hε : ε < 1) :
    ∀ᶠ x : ℝ in atTop, ∀ p ∈ markedLogPowerBand a x,
      (p : ℝ) ≤ x ^ (1 - ε) := by
  have hlim : Tendsto (fun x : ℝ => (Real.log x) ^ (a - 1)) atTop (nhds 0) := by
    simpa only [Function.comp_def, neg_sub] using
      (tendsto_rpow_neg_atTop (sub_pos.mpr ha)).comp Real.tendsto_log_atTop
  filter_upwards [hlim.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < (1 - ε) / 2)),
    eventually_gt_atTop (1 : ℝ)] with x hx hx1
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hpow : (Real.log x) ^ a = (Real.log x) ^ (a - 1) * Real.log x := by
    conv_lhs => rw [show a = (a - 1) + 1 by ring]
    rw [Real.rpow_add hlx, Real.rpow_one]
  have hlog : 2 * (Real.log x) ^ a ≤ (1 - ε) * Real.log x := by
    rw [hpow]
    nlinarith
  intro p hp
  apply (mem_markedLogPowerBand.mp hp).2.2.trans
  rw [← Real.exp_log (Real.rpow_pos_of_pos hx0 (1 - ε)), Real.log_rpow hx0]
  exact Real.exp_le_exp.mpr hlog

noncomputable def boundedGiantIndicator (n : ℕ) (x ε : ℝ) : ℝ :=
  if (giantPrimeFactors n x ε).Nonempty then 1 else 0

theorem boundedGiantIndicator_bounds (n : ℕ) (x ε : ℝ) :
    0 ≤ boundedGiantIndicator n x ε ∧ boundedGiantIndicator n x ε ≤ 1 := by
  unfold boundedGiantIndicator
  split_ifs <;> norm_num

/-- Capping changes nothing on the actual support of the prime statistic. -/
theorem boundedGiantIndicator_eq_card {n : ℕ} {x ε : ℝ}
    (hn : 0 < n) (hnx : (n : ℝ) ≤ 2 * x) (hx : 4 ≤ x) (hε : ε ≤ 1 / 4) :
    boundedGiantIndicator n x ε = (giantPrimeFactors n x ε).card := by
  have hc := giantPrimeFactors_card_zero_or_one hn hnx hx hε
  unfold boundedGiantIndicator
  rcases hc with hzero | hone
  · have he : giantPrimeFactors n x ε = ∅ := Finset.card_eq_zero.mp hzero
    simp [he]
  · have he : (giantPrimeFactors n x ε).Nonempty := Finset.card_pos.mp (by omega)
    simp [he, hone]

theorem boundedGiantIndicator_mul_small {m n : ℕ} {x ε : ℝ}
    (hm : 0 < m) (hn : 0 < n) (hsmall : (m : ℝ) ≤ x ^ (1 - ε)) :
    boundedGiantIndicator (m * n) x ε = boundedGiantIndicator n x ε := by
  unfold boundedGiantIndicator
  rw [giantPrimeFactors_mul_small hm hn hsmall]

/-- A globally bounded extension of the centered statistic, for each
normalizer in `[0,1]`. -/
theorem boundedGiantIndicator_sub_abs_le_one (n : ℕ) (x ε C : ℝ)
    (hC0 : 0 ≤ C) (hC1 : C ≤ 1) :
    |boundedGiantIndicator n x ε - C| ≤ 1 := by
  obtain ⟨h0, h1⟩ := boundedGiantIndicator_bounds n x ε
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Equation (2.4) holds simultaneously for all positive integer arguments. -/
theorem centered_giant_band_invariant_eventually {a ε : ℝ}
    (ha : a < 1) (hε : ε < 1) :
    ∀ᶠ x : ℝ in atTop, ∀ p ∈ markedLogPowerBand a x, ∀ n : ℕ, 0 < n →
      boundedGiantIndicator (p * n) x ε - giantPrimeReciprocalSum x ε =
        boundedGiantIndicator n x ε - giantPrimeReciprocalSum x ε := by
  filter_upwards [marked_band_below_giant_eventually ha hε] with x hx
  intro p hp n hn
  rw [boundedGiantIndicator_mul_small (mem_markedLogPowerBand.mp hp).1.pos hn (hx p hp)]

theorem giantPrimeConstant_lt_one {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1 / 4) :
    giantPrimeConstant ε < 1 := by
  have hden : 0 < 1 - ε := by linarith
  have hratio : (1 - ε / 2) / (1 - ε) < 2 := by
    apply (div_lt_iff₀ hden).mpr
    linarith
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)
    linarith
  exact (Real.log_lt_log (div_pos (by linarith) hden) hratio).trans hlog2

/-- The actual normalizer is eventually in the interval required for the
bounded centered extension. -/
theorem giantPrimeReciprocalSum_bounds_eventually {ε : ℝ}
    (hε : 0 < ε) (hεq : ε < 1 / 4) :
    ∀ᶠ x : ℝ in atTop,
      0 ≤ giantPrimeReciprocalSum x ε ∧ giantPrimeReciprocalSum x ε ≤ 1 := by
  have hlim := giantPrimeReciprocalSum_tendsto hε (by linarith : ε < 1)
  filter_upwards [hlim.eventually (gt_mem_nhds (giantPrimeConstant_lt_one hε hεq))]
    with x hx
  refine ⟨?_, hx.le⟩
  unfold giantPrimeReciprocalSum
  exact Finset.sum_nonneg (fun _ _ => by positivity)

/-- The three properties needed when applying the marked coefficient
criterion: a uniform global bound, exact band-prime invariance, and agreement
with the uncapped centered statistic on the original support. -/
theorem centered_giant_criterion_interface {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, a i < 1)
    {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1 / 4) :
    ∀ᶠ x : ℝ in atTop,
      (∀ n : ℕ, |boundedGiantIndicator n x ε - giantPrimeReciprocalSum x ε| ≤ 1) ∧
      (∀ i, ∀ p ∈ markedLogPowerBand (a i) x, ∀ n : ℕ, 0 < n →
        boundedGiantIndicator (p * n) x ε - giantPrimeReciprocalSum x ε =
          boundedGiantIndicator n x ε - giantPrimeReciprocalSum x ε) ∧
      (∀ n : ℕ, 0 < n → (n : ℝ) ≤ 2 * x →
        boundedGiantIndicator n x ε - giantPrimeReciprocalSum x ε =
          (giantPrimeFactors n x ε).card - giantPrimeReciprocalSum x ε) := by
  have hinv := eventually_all.mpr (fun i =>
    centered_giant_band_invariant_eventually (ha i) (by linarith : ε < 1))
  filter_upwards [giantPrimeReciprocalSum_bounds_eventually hε hεq, hinv,
    eventually_ge_atTop (4 : ℝ)] with x hC hi hx
  refine ⟨fun n => boundedGiantIndicator_sub_abs_le_one n x ε _ hC.1 hC.2, hi, ?_⟩
  intro n hn hnx
  rw [boundedGiantIndicator_eq_card hn hnx hx hεq.le]

end ArtinMatthews
