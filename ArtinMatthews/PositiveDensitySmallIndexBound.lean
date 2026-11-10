module

public import ArtinMatthews.ExceptionalAsymptotic
public import ArtinMatthews.SieveAssembly
public import ArtinMatthews.LargeFactor
public import ArtinMatthews.PositiveDensitySmallIndexCover
public import ArtinMatthews.SplittingAggregation
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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

/-! Summation of the literal uniform dyadic splitting estimate over all
index primes up to the actual growing cutoff. -/

noncomputable section
namespace ArtinMatthews

open Filter
open scoped BigOperators Topology

theorem giantSieve_indexLog_ratio_le {x ε : ℝ} {q : ℕ}
    (hx : 4 ≤ x) (hε : ε ≤ 1) (hq : 0 < q)
    (hqm : q ≤ exceptionalExponentCutoff ε x) :
    Real.log (2 * (q : ℝ)) / Real.log x ≤ 2 := by
  have hx₁ : 1 < x := by linarith
  have hx₀ : 0 < x := zero_lt_one.trans hx₁
  have hfloor : (q : ℝ) ≤ 2 * x ^ ε :=
    (Nat.cast_le.mpr hqm).trans (Nat.floor_le (by positivity))
  have hpow : x ^ ε ≤ x := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx₁.le hε
  have hqle : 2 * (q : ℝ) ≤ x ^ 2 := by
    calc
      _ ≤ 4 * x ^ ε := by linarith
      _ ≤ 4 * x := mul_le_mul_of_nonneg_left hpow (by norm_num)
      _ ≤ _ := by nlinarith [mul_nonneg hx₀.le (sub_nonneg.mpr hx)]
  have hlog := Real.log_le_log (mul_pos (by norm_num) (Nat.cast_pos.mpr hq)) hqle
  apply (div_le_iff₀ (Real.log_pos hx₁)).mpr
  simpa only [Real.log_pow, Nat.cast_ofNat] using hlog

theorem giantSieve_smallIndex_card_le_of_split {S : Finset ℤ} {P : Finset ℕ} {Y : ℕ}
    {x ε β C : ℝ} (hx : 4 ≤ x) (hε : ε ≤ 1) (hC : 0 ≤ C)
    (hY : 3 ≤ Y) (habs : ∀ a ∈ S, a.natAbs ≤ Y)
    (hP : ∀ p ∈ P, p.Prime ∧ (x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x) ∧
      ∀ a ∈ S, (a : ZMod p) ≠ 0)
    (havoid : ∀ p ∈ P, ∀ a ∈ S, ∀ q, q.Prime → q ≤ Y → ¬ q ∣ multiplicativeIndex p a)
    (hsplit : ∀ a ∈ S, ∀ q : ℕ, q.Prime → 2 < q → a.natAbs ≤ q →
      ∀ R : Finset Nat.Primes,
        (∀ p ∈ R, x ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧
          ¬ (p.val : ℤ) ∣ (q : ℤ) ∧ (a : ZMod p.val) ≠ 0 ∧ q ∣ multiplicativeIndex p a) →
        (R.card : ℝ) ≤ C * (x / ((q : ℝ) * ((q : ℝ) - 1) * Real.log x) +
          x ^ β * Real.log (2 * (q : ℝ)) / Real.log x)) :
    ((smallIndexCandidates S P (exceptionalExponentCutoff ε x)).card : ℝ) ≤
      (C * (S.card : ℝ) / Y) * (x / Real.log x) +
        4 * C * (S.card : ℝ) * x ^ (β + ε) := by
  let m := exceptionalExponentCutoff ε x
  let Q := giantSieveRemainingIndexPrimes Y m
  let X := C * (x / Real.log x)
  let E := 2 * C * x ^ β
  have hx₁ : 1 < x := by linarith
  have hx₀ := zero_lt_one.trans hx₁
  have hY₀ : 0 < Y := by omega
  have hX : 0 ≤ X := mul_nonneg hC (div_nonneg hx₀.le (Real.log_pos hx₁).le)
  have hE : 0 ≤ E := mul_nonneg (mul_nonneg (by norm_num) hC) (Real.rpow_nonneg hx₀.le _)
  have hQcard : (Q.card : ℝ) ≤ 2 * x ^ ε :=
    (Nat.cast_le.mpr (giantSieveRemainingIndexPrimes_card_le Y m)).trans
      (Nat.floor_le (by positivity))
  have hfiber (a : ℤ) (ha : a ∈ S) (q : ℕ) (hq : q ∈ Q) :
      ((giantSieveIndexFiber P a q).card : ℝ) ≤ X / ((q : ℝ) * ((q : ℝ) - 1)) + E := by
    obtain ⟨hprime, hqY, hqm⟩ := mem_giantSieveRemainingIndexPrimes.mp hq
    let hPr : ∀ p ∈ P, p.Prime := fun p hp => (hP p hp).1
    let R := giantSievePrimeIndexFiber P hPr a q
    have hR : ∀ p ∈ R, x ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧
        ¬ (p.val : ℤ) ∣ (q : ℤ) ∧ (a : ZMod p.val) ≠ 0 ∧ q ∣ multiplicativeIndex p a := by
      intro p hp
      obtain ⟨hpP, hd⟩ := mem_giantSievePrimeIndexFiber.mp hp
      obtain ⟨hpr, hpi, hn⟩ := hP p.val hpP
      have ha₀ := hn a ha
      have hqp : q < p.val :=
        (Nat.le_of_dvd (Nat.sub_pos_of_lt hpr.one_lt)
          (hd.trans (multiplicativeIndex_dvd hpr ha₀))).trans_lt (Nat.sub_lt hpr.pos Nat.one_pos)
      refine ⟨hpi.1.le, hpi.2, ?_, ha₀, hd⟩
      intro hdvd
      exact (not_le_of_gt hqp) (Nat.le_of_dvd hprime.pos (Int.natCast_dvd_natCast.mp hdvd))
    have hbound := hsplit a ha q hprime (by omega) ((habs a ha).trans hqY.le) R hR
    change ((giantSievePrimeIndexFiber P hPr a q).card : ℝ) ≤ _ at hbound
    rw [giantSievePrimeIndexFiber_card] at hbound
    have hratio := giantSieve_indexLog_ratio_le hx hε hprime.pos hqm
    calc
      _ ≤ C * (x / ((q : ℝ) * ((q : ℝ) - 1) * Real.log x) +
          x ^ β * Real.log (2 * (q : ℝ)) / Real.log x) := hbound
      _ ≤ C * (x / ((q : ℝ) * ((q : ℝ) - 1) * Real.log x) + x ^ β * 2) := by
        rw [mul_div_assoc (x ^ β)]
        exact mul_le_mul_of_nonneg_left (add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hratio (Real.rpow_nonneg hx₀.le _))) hC
      _ = _ := by
        simp only [X, E, div_eq_mul_inv, mul_inv_rev]
        ring
  calc
    _ ≤ ∑ a ∈ S, ∑ q ∈ Q, ((giantSieveIndexFiber P a q).card : ℝ) :=
      giantSieve_smallIndex_card_le_sum S P Y m havoid
    _ ≤ ∑ _a ∈ S, (X / (Y : ℝ) + (Q.card : ℝ) * E) := by
      apply Finset.sum_le_sum
      intro a ha
      exact sum_splitting_bounds hY₀ (fun q hq => (mem_giantSieveRemainingIndexPrimes.mp hq).2.1)
        hX (hfiber a ha)
    _ ≤ ∑ _a ∈ S, (X / (Y : ℝ) + (2 * x ^ ε) * E) :=
      Finset.sum_le_sum fun _ _ => add_le_add le_rfl (mul_le_mul_of_nonneg_right hQcard hE)
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, X, E, Real.rpow_add hx₀]
      ring

theorem giantSieve_index_error_isLittleO (K : ℝ) {δ ε : ℝ} (hεδ : ε < δ) :
    (fun x : ℝ => K * x ^ (1 - δ + ε)) =o[atTop] (fun x : ℝ => x / Real.log x) := by
  have h := ((isLittleO_log_rpow_atTop (sub_pos.mpr hεδ)).tendsto_div_nhds_zero).const_mul K
  simp only [mul_zero] at h
  apply Asymptotics.isLittleO_of_tendsto' _
  · apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx₀ := zero_lt_one.trans hx
    have hpow : x ^ (1 - δ + ε) = x / x ^ (δ - ε) := by
      rw [show 1 - δ + ε = 1 - (δ - ε) by ring, Real.rpow_sub hx₀, Real.rpow_one]
    rw [hpow]
    field_simp
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    intro hz
    exact False.elim ((ne_of_gt (div_pos (zero_lt_one.trans hx) (Real.log_pos hx))) hz)

end ArtinMatthews
