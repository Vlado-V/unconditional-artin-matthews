module

public import ArtinMatthews.MarkedBonferroniTail
public import ArtinMatthews.MarkedProgressionDepthGrowth
public import ArtinMatthews.MarkedProgressionLocalDecay
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

/-! All-logarithmic decay of the explicit arithmetic error envelope.
No distribution estimate is assumed: the three terms are bounded using
subpolynomial retained mass, the lower prime endpoint, and a factorial tail. -/

namespace ArtinMatthews

open Filter
open scoped Asymptotics Topology

/-- The odd omitted layer at the actual even Bonferroni depth saves every
fixed power of the logarithm. -/
theorem markedFactorialTail_even_log_depth_tendsto {V δ : ℝ}
    (hV : 0 ≤ V) (hδ : 0 < δ) (A : ℝ) :
    Tendsto (fun x : ℝ => (Real.log x) ^ A *
      markedFactorialTail V (2 * ⌊(Real.log x) ^ δ⌋₊ + 1)) atTop (𝓝 0) := by
  have hpow : Tendsto (fun t : ℝ => t ^ A *
      markedFactorialTail V (2 * ⌊t ^ δ⌋₊ + 1)) atTop (𝓝 0) := by
    have hbound := (rpow_mul_exp_neg_rpow_tendsto A hδ
      (Real.log_pos (by norm_num : (1 : ℝ) < 2))).const_mul (Real.exp (2 * V))
    simp only [mul_zero] at hbound
    apply squeeze_zero' _ _ hbound
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      exact mul_nonneg (Real.rpow_nonneg ht.le _) (markedFactorialTail_nonneg hV _)
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      have hn : t ^ δ ≤ ((2 * ⌊t ^ δ⌋₊ + 1 : ℕ) : ℝ) := by
        have hfloor := (Nat.lt_floor_add_one (t ^ δ)).le
        push_cast
        nlinarith [show (0 : ℝ) ≤ (⌊t ^ δ⌋₊ : ℝ) from Nat.cast_nonneg _]
      have hh := mul_le_mul_of_nonneg_left
        (markedFactorialTail_le_exp hV (2 * ⌊t ^ δ⌋₊ + 1) hn)
        (Real.rpow_nonneg ht.le A)
      convert hh using 1
      ring
  exact hpow.comp Real.tendsto_log_atTop

/-- A real fixed shift is harmless in the local coprimality loss. -/
theorem marked_real_shift_local_loss_log_depth_tendsto (δ A s : ℝ)
    {α : ℝ} (hα : 0 < α) :
    Tendsto (fun x : ℝ => (s + ((2 * ⌊(Real.log x) ^ δ⌋₊ : ℕ) : ℝ)) *
      (Real.log x) ^ A / Real.exp ((Real.log x) ^ α)) atTop (𝓝 0) := by
  have hconstant := (marked_local_loss_scaled_log_depth_tendsto δ A 0 1 hα).const_mul s
  have hdepth := marked_local_loss_scaled_log_depth_tendsto δ A 2 0 hα
  have h := hconstant.add hdepth
  simp only [mul_zero, zero_add] at h
  apply h.congr'
  filter_upwards [] with x
  simp only [Nat.zero_mul, Nat.zero_add, Nat.cast_one, one_mul, Nat.add_zero]
  ring

/-- The retained coefficient mass and divisor level leave a power saving
after summation through any fixed exponent `c < 1`. -/
theorem marked_rounding_envelope_tendsto (δ β c A : ℝ) (K : ℕ)
    (hδ : 0 < δ) (hβ : 0 < β) (hsum : δ + β < 1) (hc : c < 1) :
    Tendsto (fun x : ℝ => (Real.log x) ^ A / x *
      (x ^ c * ((2 * ⌊(Real.log x) ^ δ⌋₊ + 2 : ℕ) : ℝ) *
        (Real.exp (2 * (Real.log x) ^ β)) ^ (2 * ⌊(Real.log x) ^ δ⌋₊ + 1 + K)))
      atTop (𝓝 0) := by
  let ε : ℝ := (1 - c) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hbound := (isLittleO_log_rpow_rpow_atTop A hε).tendsto_div_nhds_zero
  apply squeeze_zero' _ _ hbound
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have hlog := Real.log_pos hx
    positivity
  · filter_upwards [eventually_gt_atTop (1 : ℝ),
      marked_scaled_truncation_power_le_rpow_eventually δ β 2 1 K ε hδ hβ hsum hε]
      with x hx hmass
    have hx0 : 0 < x := by linarith
    have hlog := Real.log_pos hx
    have hmass' : ((2 * ⌊(Real.log x) ^ δ⌋₊ + 2 : ℕ) : ℝ) *
        (Real.exp (2 * (Real.log x) ^ β)) ^ (2 * ⌊(Real.log x) ^ δ⌋₊ + 1 + K) ≤ x ^ ε := by
      simpa only [Nat.add_assoc] using hmass
    have hp : x ^ c * x ^ ε * x ^ ε = x := by
      rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
      have he : c + ε + ε = 1 := by dsimp [ε]; ring
      rw [he, Real.rpow_one]
    calc
      _ = ((Real.log x) ^ A / x * x ^ c) *
          (((2 * ⌊(Real.log x) ^ δ⌋₊ + 2 : ℕ) : ℝ) *
            (Real.exp (2 * (Real.log x) ^ β)) ^ (2 * ⌊(Real.log x) ^ δ⌋₊ + 1 + K)) := by ring
      _ ≤ ((Real.log x) ^ A / x * x ^ c) * x ^ ε :=
        mul_le_mul_of_nonneg_left hmass' (by positivity)
      _ = (Real.log x) ^ A / x ^ ε := by
        apply (eq_div_iff (Real.rpow_pos_of_pos hx0 ε).ne').mpr
        calc
          _ = ((Real.log x) ^ A / x) * (x ^ c * x ^ ε * x ^ ε) := by ring
          _ = (Real.log x) ^ A := by rw [hp, div_mul_cancel₀ _ hx0.ne']

/-- The explicit error arising from the finite progression argument.
Here the upper prime endpoint is `exp (2*(log x)^β)`, the lower endpoint
is `exp ((log x)^α)`, and the even truncation depth is `2*floor((log x)^δ)`. -/
noncomputable def markedProgressionEnvelope (x α β δ c s V : ℝ) (K : ℕ) : ℝ :=
  let m := ⌊(Real.log x) ^ δ⌋₊
  x ^ c * ((2 * m + 2 : ℕ) : ℝ) * (Real.exp (2 * (Real.log x) ^ β)) ^ (2 * m + 1 + K) +
    x * (1 + Real.log x) *
      (((s + ((2 * m : ℕ) : ℝ)) / Real.exp ((Real.log x) ^ α)) * Real.exp V +
        2 * markedFactorialTail V (2 * m + 1))

/-- Every prescribed logarithmic power is saved by the actual arithmetic
error envelope. The real shift `s` is arbitrary, and only `c < 1` is needed. -/
theorem markedProgressionEnvelope_tendsto (α β δ c s V A : ℝ) (K : ℕ)
    (hα : 0 < α) (hβ : 0 < β) (hδ : 0 < δ) (hsum : δ + β < 1)
    (hc : c < 1) (hV : 0 ≤ V) :
    Tendsto (fun x : ℝ => (Real.log x) ^ A / x *
      markedProgressionEnvelope x α β δ c s V K) atTop (𝓝 0) := by
  have hround := marked_rounding_envelope_tendsto δ β c A K hδ hβ hsum hc
  have hlocal := ((marked_real_shift_local_loss_log_depth_tendsto δ A s hα).add
    (marked_real_shift_local_loss_log_depth_tendsto δ (A + 1) s hα)).mul_const (Real.exp V)
  have htail := ((markedFactorialTail_even_log_depth_tendsto hV hδ A).add
    (markedFactorialTail_even_log_depth_tendsto hV hδ (A + 1))).const_mul 2
  have h := hround.add (hlocal.add htail)
  simp only [zero_add, zero_mul, mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  have hlog := Real.log_pos hx
  dsimp only [markedProgressionEnvelope]
  rw [Real.rpow_add hlog, Real.rpow_one]
  field_simp

/-- Equivalently, the error divided by the ambient length is smaller than
every fixed negative logarithmic power. -/
theorem markedProgressionEnvelope_isLittleO (α β δ c s V A : ℝ) (K : ℕ)
    (hα : 0 < α) (hβ : 0 < β) (hδ : 0 < δ) (hsum : δ + β < 1)
    (hc : c < 1) (hV : 0 ≤ V) :
    (fun x : ℝ => markedProgressionEnvelope x α β δ c s V K / x) =o[atTop]
      (fun x : ℝ => (Real.log x) ^ (-A)) := by
  apply Asymptotics.isLittleO_of_tendsto'
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact fun h => (Real.rpow_pos_of_pos (Real.log_pos hx) (-A)).ne' h |>.elim
  · apply (markedProgressionEnvelope_tendsto α β δ c s V A K
      hα hβ hδ hsum hc hV).congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    rw [Real.rpow_neg (Real.log_pos hx).le, div_inv_eq_mul]
    ring

end ArtinMatthews
