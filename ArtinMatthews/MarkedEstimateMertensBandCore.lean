module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
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

/-!
# Finite prime intervals used by the marked estimates

The lower boundary of a real prime interval changes its reciprocal mass by
at most the reciprocal of that boundary. These finite facts preserve the
closed lower endpoint in the manuscript's marking bands.
-/

namespace ArtinMatthews

open scoped BigOperators

/-- The exact marking band in Section 2, including both endpoints. -/
noncomputable def markedLogPowerBand (a x : ℝ) : Finset ℕ := by
  classical
  exact (Nat.primesLE ⌊Real.exp (2 * (Real.log x) ^ a)⌋₊).filter
    (fun p : ℕ => Real.exp ((Real.log x) ^ a) ≤ (p : ℝ))

theorem mem_markedLogPowerBand {a x : ℝ} {p : ℕ} :
    p ∈ markedLogPowerBand a x ↔ p.Prime ∧
      Real.exp ((Real.log x) ^ a) ≤ (p : ℝ) ∧
      (p : ℝ) ≤ Real.exp (2 * (Real.log x) ^ a) := by
  classical
  simp only [markedLogPowerBand, Finset.mem_filter, Nat.mem_primesLE,
    Nat.le_floor_iff (Real.exp_nonneg _)]
  tauto

/-- Distinct fixed band exponents give disjoint bands for all sufficiently
large parameters, as required by the independent divisor model. -/
theorem markedLogPowerBand_disjoint_eventually {a b : ℝ} (hab : a < b) :
    ∀ᶠ x : ℝ in Filter.atTop, Disjoint (markedLogPowerBand a x) (markedLogPowerBand b x) := by
  have hpow := (tendsto_rpow_atTop (sub_pos.mpr hab)).comp Real.tendsto_log_atTop
  filter_upwards [hpow.eventually (Filter.eventually_gt_atTop (2 : ℝ)),
    Real.tendsto_log_atTop.eventually (Filter.eventually_gt_atTop (0 : ℝ))] with x hpow hlog
  change (2 : ℝ) < (Real.log x) ^ (b - a) at hpow
  apply Finset.disjoint_left.mpr
  intro p hpa hpb
  obtain ⟨_, _, hpa⟩ := mem_markedLogPowerBand.mp hpa
  obtain ⟨_, hpb, _⟩ := mem_markedLogPowerBand.mp hpb
  have hpos := Real.rpow_pos_of_pos hlog a
  have hsplit : (Real.log x) ^ b = (Real.log x) ^ a * (Real.log x) ^ (b - a) := by
    rw [← Real.rpow_add hlog]
    congr 1
    ring
  have hexp : Real.exp (2 * (Real.log x) ^ a) < Real.exp ((Real.log x) ^ b) := by
    apply Real.exp_lt_exp.mpr
    rw [hsplit]
    nlinarith
  linarith

noncomputable def markedPrimePrefix (y : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊y⌋₊, (1 : ℝ) / p

noncomputable def markedOpenBandMass (y z : ℝ) : ℝ := by
  classical
  exact ∑ p ∈ (Nat.primesLE ⌊z⌋₊).filter (fun p : ℕ => y < (p : ℝ)), (1 : ℝ) / p

noncomputable def markedClosedBandMass (y z : ℝ) : ℝ := by
  classical
  exact ∑ p ∈ (Nat.primesLE ⌊z⌋₊).filter (fun p : ℕ => y ≤ (p : ℝ)), (1 : ℝ) / p

/-- Closing a positive real lower boundary inserts at most one integer. -/
theorem reciprocal_boundary_mass_le (S : Finset ℕ) {y : ℝ} (hy : 0 < y) :
    |(∑ p ∈ S.filter (fun p : ℕ => y ≤ (p : ℝ)), (1 : ℝ) / p) -
      (∑ p ∈ S.filter (fun p : ℕ => y < (p : ℝ)), (1 : ℝ) / p)| ≤ 1 / y := by
  classical
  let E := S.filter (fun p : ℕ => y = (p : ℝ))
  have hsplit : (∑ p ∈ S.filter (fun p : ℕ => y ≤ (p : ℝ)), (1 : ℝ) / p) =
      (∑ p ∈ S.filter (fun p : ℕ => y < (p : ℝ)), (1 : ℝ) / p) +
        ∑ p ∈ E, (1 : ℝ) / p := by
    simp only [E, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    rcases lt_trichotomy y (p : ℝ) with h | h | h
    · simp [h, h.le, h.ne]
    · simp [h]
    · simp [not_le.mpr h, not_lt.mpr h.le, ne_of_gt h]
  have hcard : E.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp q hq
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    exact_mod_cast hp'.symm.trans hq'
  have hsum : (∑ p ∈ E, (1 : ℝ) / p) = E.card * (1 / y) := by
    calc
      _ = ∑ _p ∈ E, 1 / y := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [← (Finset.mem_filter.mp hp).2]
      _ = _ := by simp
  rw [hsplit, add_sub_cancel_left, hsum, abs_of_nonneg (by positivity)]
  exact mul_le_of_le_one_left (by positivity) (by exact_mod_cast hcard)

theorem markedClosedBandMass_sub_open_le {y z : ℝ} (hy : 0 < y) :
    |markedClosedBandMass y z - markedOpenBandMass y z| ≤ 1 / y :=
  reciprocal_boundary_mass_le (Nat.primesLE ⌊z⌋₊) hy

/-- The half-open interval is exactly a difference of cumulative prime sums. -/
theorem markedOpenBandMass_eq_sub {y z : ℝ} (hy : 0 ≤ y) (hyz : y ≤ z) :
    markedOpenBandMass y z = markedPrimePrefix z - markedPrimePrefix y := by
  classical
  have hsub : Nat.primesLE ⌊y⌋₊ ⊆ Nat.primesLE ⌊z⌋₊ := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_mem_primesLE hp).trans (Nat.floor_mono hyz),
      Nat.prime_of_mem_primesLE hp⟩
  have hset : (Nat.primesLE ⌊z⌋₊).filter (fun p : ℕ => y < (p : ℝ)) =
      Nat.primesLE ⌊z⌋₊ \ Nat.primesLE ⌊y⌋₊ := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_sdiff, Nat.mem_primesLE]
    constructor
    · rintro ⟨hp, hpy⟩
      refine ⟨hp, fun hp' => ?_⟩
      exact (not_le_of_gt hpy) ((Nat.cast_le.mpr hp'.1).trans (Nat.floor_le hy))
    · rintro ⟨hp, hpy⟩
      refine ⟨hp, ?_⟩
      by_contra h
      exact hpy ⟨(Nat.le_floor_iff hy).mpr (le_of_not_gt h), hp.2⟩
  unfold markedOpenBandMass markedPrimePrefix
  rw [hset, Finset.sum_sdiff_eq_sub hsub]

/-- Closing the lower boundary leaves the Mertens interval limit unchanged.
The assumptions here expose exactly the cumulative-prime input; the concrete
Mertens theorem is applied in `MarkedEstimateMertensBands.lean`. -/
theorem marked_exponential_band_mass_tendsto_of_prefix
    (M : ℝ) (E : ℝ → ℝ)
    (hE : Filter.Tendsto E Filter.atTop (nhds 0))
    (hprefix : ∀ y, markedPrimePrefix y = Real.log (Real.log y) + M + E y) :
    Filter.Tendsto
      (fun T : ℝ => markedClosedBandMass (Real.exp T) (Real.exp (2 * T)))
      Filter.atTop (nhds (Real.log 2)) := by
  have hE₁ := hE.comp Real.tendsto_exp_atTop
  have hE₂ := hE.comp (Real.tendsto_exp_atTop.comp
    (Filter.tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)))
  have hopen : Filter.Tendsto
      (fun T : ℝ => markedOpenBandMass (Real.exp T) (Real.exp (2 * T)))
      Filter.atTop (nhds (Real.log 2)) := by
    have h := (hE₂.sub hE₁).const_add (Real.log 2)
    simp only [sub_self, add_zero] at h
    apply h.congr'
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with T hT
    rw [markedOpenBandMass_eq_sub (Real.exp_nonneg _)
      (Real.exp_le_exp.mpr (by linarith)), hprefix, hprefix,
      Real.log_exp, Real.log_exp,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : T ≠ 0)]
    simp only [Function.comp_apply, id_eq]
    ring
  have hinv : Filter.Tendsto (fun T : ℝ => 1 / Real.exp T)
      Filter.atTop (nhds 0) := by
    simpa only [one_div, Real.exp_neg] using Real.tendsto_exp_neg_atTop_nhds_zero
  have hdiff : Filter.Tendsto
      (fun T : ℝ => markedClosedBandMass (Real.exp T) (Real.exp (2 * T)) -
        markedOpenBandMass (Real.exp T) (Real.exp (2 * T)))
      Filter.atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) _ hinv
    exact Filter.Eventually.of_forall fun T => by
      simpa only [Real.norm_eq_abs] using
        markedClosedBandMass_sub_open_le (z := Real.exp (2 * T)) (Real.exp_pos T)
  simpa only [sub_add_cancel, zero_add] using hdiff.add hopen

end ArtinMatthews
