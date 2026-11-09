module

public import ArtinMatthews.MarkedBonferroniTail
public import Mathlib.Analysis.SpecialFunctions.Sqrt


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform absorption of the actual prime-power error in the short major-arc
prime-cancellation estimate. -/
noncomputable section
namespace ArtinMatthews

open Filter
open scoped Topology

/-- The literal prime-power expression has a uniform exponential envelope. -/
theorem marked_major_prime_power_envelope (η τ L u v : ℝ)
    (hτ : 0 < τ) (_hη : 0 < η) (hL : 0 ≤ L)
    (hu : Real.exp (τ * L) ≤ u) (huv : u ≤ v)
    (hvu : v ≤ 2 * u) (hv : v ≤ Real.exp (η * L)) :
    2 * Real.sqrt v * Real.log v / u ≤
      4 * η * L * Real.exp (-(τ / 2) * L) := by
  have hu0 : 0 < u := lt_of_lt_of_le (Real.exp_pos _) hu
  have hv0 : 0 < v := hu0.trans_le huv
  have hs0 : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv0
  have h1 : 1 ≤ v :=
    ((Real.one_le_exp_iff.mpr (mul_nonneg hτ.le hL)).trans hu).trans huv
  have hlog0 : 0 ≤ Real.log v := Real.log_nonneg h1
  have hlog : Real.log v ≤ η * L := by
    simpa only [Real.log_exp] using Real.log_le_log hv0 hv
  have hs : Real.exp ((τ / 2) * L) ≤ Real.sqrt v := by
    have hh := Real.sqrt_le_sqrt (hu.trans huv)
    rw [← Real.exp_half] at hh
    calc
      Real.exp ((τ / 2) * L) = Real.exp ((τ * L) / 2) :=
        congrArg Real.exp (by ring)
      _ ≤ Real.sqrt v := hh
  have hq : Real.sqrt v / u ≤ 2 / Real.sqrt v := by
    apply (div_le_div_iff₀ hu0 hs0).mpr
    nlinarith [Real.sq_sqrt hv0.le]
  have hr : 2 / Real.sqrt v ≤ 2 * Real.exp (-(τ / 2) * L) := by
    have hh := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
      (Real.exp_pos ((τ / 2) * L)) hs
    simpa only [div_eq_mul_inv, ← Real.exp_neg, neg_mul] using hh
  calc
    _ = 2 * (Real.sqrt v / u) * Real.log v := by ring
    _ ≤ 2 * (2 * Real.exp (-(τ / 2) * L)) * Real.log v :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hq.trans hr) (by norm_num)) hlog0
    _ ≤ 2 * (2 * Real.exp (-(τ / 2) * L)) * (η * L) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = _ := by ring

/-- Every prescribed logarithmic power absorbs the exponential envelope. -/
theorem marked_major_prime_power_envelope_uniform_power (A η τ c : ℝ)
    (hA : 0 ≤ A) (hτ : 0 < τ) (_hη : 0 < η) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
      4 * η * L * Real.exp (-(τ / 2) * L) ≤ c * L ^ (-A) := by
  have ht : Tendsto (fun L : ℝ =>
      4 * η * (L ^ (A + 1) * Real.exp (-(τ / 2) * L))) atTop (𝓝 0) := by
    simpa only [Real.rpow_one, mul_zero] using
      (rpow_mul_exp_neg_rpow_tendsto (A + 1)
        (δ := 1) (b := τ / 2) (by norm_num) (half_pos hτ)).const_mul (4 * η)
  have he := ht.eventually (gt_mem_nhds hc)
  filter_upwards [he, eventually_ge_atTop (1 : ℝ)] with L hsmall hL
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hp : 0 < L ^ A := zero_lt_one.trans_le (Real.one_le_rpow hL hA)
  rw [Real.rpow_neg hL0.le, ← div_eq_mul_inv]
  apply (le_div_iff₀ hp).mpr
  rw [Real.rpow_add hL0, Real.rpow_one] at hsmall
  convert hsmall.le using 1
  ring

/-- The actual prime-power error is uniformly smaller than any fixed power
throughout the major-arc interval range. -/
theorem marked_major_prime_power_uniform_power (A η τ c : ℝ)
    (hA : 0 ≤ A) (hτ : 0 < τ) (hη : 0 < η) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ u v : ℝ,
      Real.exp (τ * L) ≤ u → u ≤ v → v ≤ 2 * u → v ≤ Real.exp (η * L) →
        2 * Real.sqrt v * Real.log v / u ≤ c * L ^ (-A) := by
  filter_upwards [marked_major_prime_power_envelope_uniform_power A η τ c hA hτ hη hc,
    eventually_ge_atTop (0 : ℝ)] with L hpower hL u v hu huv hvu hv
  exact (marked_major_prime_power_envelope η τ L u v hτ hη hL hu huv hvu hv).trans hpower

end ArtinMatthews
