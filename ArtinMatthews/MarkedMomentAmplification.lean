module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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


set_option backward.privateInPublic true
@[expose] public section

/-! Exact pure amplification proofs reused from OpenAI math-main:
MRTAmplificationPower, MRTNoSmallSamples (cost definition only), and
MRTSampleCost. The original source identifiers and extraction hashes are
recorded in verification/marked-moment-amplification-provenance.json.
Only the import context and namespace differ from the extracted source;
no arithmetic claim is assumed from the surrounding MRT application. -/

namespace ArtinMatthews.ReusedMoments

noncomputable def mrtAmplificationOrder (Y u : ℝ) : ℕ :=
  ⌈Real.log u / Real.log Y⌉₊

lemma mrt_nat_pow_eq_exp {Y : ℝ} (hY : 0 < Y) (r : ℕ) :
    Y ^ r = Real.exp ((r : ℝ) * Real.log Y) := by
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos hY]
  congr 1
  ring

theorem mrt_amplification_order_bounds {Y u : ℝ} (hY : 1 < Y) (hu : 1 ≤ u) :
    u ≤ Y ^ mrtAmplificationOrder Y u ∧
      Y ^ mrtAmplificationOrder Y u ≤ u * Y ∧
      (mrtAmplificationOrder Y u : ℝ) < Real.log u / Real.log Y + 1 := by
  have hY0 : 0 < Y := by linarith
  have hu0 : 0 < u := by linarith
  have hlogY : 0 < Real.log Y := Real.log_pos hY
  have hquot : 0 ≤ Real.log u / Real.log Y :=
    div_nonneg (Real.log_nonneg hu) hlogY.le
  have hlo : Real.log u / Real.log Y ≤ (mrtAmplificationOrder Y u : ℝ) :=
    Nat.le_ceil _
  have hhi : (mrtAmplificationOrder Y u : ℝ) < Real.log u / Real.log Y + 1 :=
    Nat.ceil_lt_add_one hquot
  refine ⟨?_, ?_, hhi⟩
  · calc
      u = Real.exp (Real.log u) := (Real.exp_log hu0).symm
      _ ≤ Real.exp ((mrtAmplificationOrder Y u : ℝ) * Real.log Y) :=
        Real.exp_le_exp.mpr ((div_le_iff₀ hlogY).mp hlo)
      _ = _ := (mrt_nat_pow_eq_exp hY0 _).symm
  · have hh : (mrtAmplificationOrder Y u : ℝ) * Real.log Y <
        Real.log u + Real.log Y := by
      have hh := (mul_lt_mul_of_pos_right hhi hlogY)
      rw [add_mul, div_mul_cancel₀ _ hlogY.ne', one_mul] at hh
      exact hh
    calc
      _ = Real.exp ((mrtAmplificationOrder Y u : ℝ) * Real.log Y) :=
        mrt_nat_pow_eq_exp hY0 _
      _ ≤ Real.exp (Real.log u + Real.log Y) := Real.exp_le_exp.mpr hh.le
      _ = u * Y := by rw [Real.exp_add, Real.exp_log hu0, Real.exp_log hY0]

noncomputable def mrtShortPrimeSampleCost (Y V T : ℝ) (r : ℕ) : ℝ :=
  (8*Real.exp 1*(T+1+((2*⌈Y⌉₊)^r:ℕ)) *
    (2+(Real.log ((2*⌈Y⌉₊)^r:ℕ))^2) * (r.factorial:ℝ)*(2/Y)^r)/V^(2*r)

/-- Once Y^r reaches the height, all ambient-height and rounding factors
are absorbed into an explicit exponential in the moment order. -/
theorem mrt_short_prime_sample_cost_le {Y V T : ℝ} (hY : 1 ≤ Y)
    (hV : 0 < V) {r : ℕ} (hTr : T ≤ Y^r) :
    mrtShortPrimeSampleCost Y V T r ≤
      24*Real.exp 1*(2+((r:ℝ)*Real.log (4*Y))^2)*(8*(r:ℝ))^r/V^(2*r) := by
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hc : Y ≤ (⌈Y⌉₊:ℝ) := Nat.le_ceil Y
  have hc' := Nat.ceil_lt_add_one hY0.le
  have hn1 : (1:ℝ) ≤ ((2*⌈Y⌉₊:ℕ):ℝ) := by push_cast; linarith
  have hn0 : (0:ℝ) < ((2*⌈Y⌉₊:ℕ):ℝ) := by linarith
  have hnle : ((2*⌈Y⌉₊:ℕ):ℝ) ≤ 4*Y := by push_cast; linarith
  have hnpr : (((2*⌈Y⌉₊)^r:ℕ):ℝ) ≤ (4*Y)^r := by
    rw [Nat.cast_pow]
    exact pow_le_pow_left₀ hn0.le hnle r
  have ht' : T ≤ (4*Y)^r := hTr.trans
    (pow_le_pow_left₀ hY0.le (by linarith) r)
  have hpow1 : (1:ℝ) ≤ (4*Y)^r := one_le_pow₀ (by linarith)
  have htime : T+1+(((2*⌈Y⌉₊)^r:ℕ):ℝ) ≤ 3*(4*Y)^r := by linarith
  have hlog : Real.log (((2*⌈Y⌉₊)^r:ℕ):ℝ) ≤ (r:ℝ)*Real.log (4*Y) := by
    rw [Nat.cast_pow, Real.log_pow]
    exact mul_le_mul_of_nonneg_left (Real.log_le_log hn0 hnle) (Nat.cast_nonneg _)
  have hlog0 : 0 ≤ Real.log (((2*⌈Y⌉₊)^r:ℕ):ℝ) := by
    apply Real.log_nonneg
    simpa only [Nat.cast_pow] using one_le_pow₀ hn1 (n := r)
  have hlog2 : 2+(Real.log (((2*⌈Y⌉₊)^r:ℕ):ℝ))^2 ≤
      2+((r:ℝ)*Real.log (4*Y))^2 := by
    have hh := pow_le_pow_left₀ hlog0 hlog 2
    linarith
  have hfac : (r.factorial:ℝ) ≤ (r:ℝ)^r := by exact_mod_cast Nat.factorial_le_pow r
  have hb : (4*Y)^r*(r:ℝ)^r*(2/Y)^r = (8*(r:ℝ))^r := by
    rw [← mul_pow, ← mul_pow]
    congr 1
    field_simp
    ring
  unfold mrtShortPrimeSampleCost
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h1 := mul_le_mul_of_nonneg_left htime (show 0 ≤ 8*Real.exp 1 by positivity)
  have h2 := mul_le_mul h1 hlog2 (by positivity) (by positivity)
  have h3 := mul_le_mul h2 hfac (by positivity) (by positivity)
  calc
    _ ≤ (8*Real.exp 1*(3*(4*Y)^r)*(2+((r:ℝ)*Real.log (4*Y))^2)*
        (r:ℝ)^r)*(2/Y)^r := mul_le_mul_of_nonneg_right h3 (by positivity)
    _ = 24*Real.exp 1*(2+((r:ℝ)*Real.log (4*Y))^2)*
        ((4*Y)^r*(r:ℝ)^r*(2/Y)^r) := by ring
    _ = _ := by rw [hb]

/-- The exact ceiling moment realizes the preceding height balance. -/
theorem mrt_short_prime_sample_cost_chosen {Y V T : ℝ} (hY : 1 < Y)
    (hV : 0 < V) (hT : 1 ≤ T) :
    mrtShortPrimeSampleCost Y V T (mrtAmplificationOrder Y T) ≤
      24*Real.exp 1*
        (2+((mrtAmplificationOrder Y T:ℝ)*Real.log (4*Y))^2)*
        (8*(mrtAmplificationOrder Y T:ℝ))^(mrtAmplificationOrder Y T)/
        V^(2*mrtAmplificationOrder Y T) :=
  mrt_short_prime_sample_cost_le hY.le hV (mrt_amplification_order_bounds hY hT).1

/-- An exponential form suitable for the small fixed extra-band exponent. -/
theorem mrt_short_prime_sample_cost_exp {Y V T : ℝ} (hY : 1 < Y)
    (hV : 0 < V) (hT : 1 < T) :
    mrtShortPrimeSampleCost Y V T (mrtAmplificationOrder Y T) ≤
      24*Real.exp 1*
        (2+((mrtAmplificationOrder Y T:ℝ)*Real.log (4*Y))^2)*
        Real.exp ((mrtAmplificationOrder Y T:ℝ)*
          (Real.log (8*(mrtAmplificationOrder Y T:ℝ))-2*Real.log V)) := by
  let r := mrtAmplificationOrder Y T
  have hr : 0 < r := by
    dsimp [r, mrtAmplificationOrder]
    exact Nat.ceil_pos.mpr (div_pos (Real.log_pos hT) (Real.log_pos hY))
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have he : (8*(r:ℝ))^r/V^(2*r) =
      Real.exp ((r:ℝ)*(Real.log (8*(r:ℝ))-2*Real.log V)) := by
    rw [mrt_nat_pow_eq_exp (by positivity), mrt_nat_pow_eq_exp hV, ← Real.exp_sub]
    congr 1
    push_cast
    ring
  have hh := mrt_short_prime_sample_cost_chosen hY hV hT.le
  change mrtShortPrimeSampleCost Y V T r ≤ _ at hh ⊢
  calc
    _ ≤ (24*Real.exp 1*(2+((r:ℝ)*Real.log (4*Y))^2))*
        ((8*(r:ℝ))^r/V^(2*r)) := by simpa only [mul_div_assoc] using hh
    _ = _ := by rw [he]

end ArtinMatthews.ReusedMoments
