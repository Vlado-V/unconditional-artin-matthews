module

public import ArtinMatthews.MarkedDeweightingParameter
public import Mathlib.Analysis.SpecialFunctions.Exp


set_option backward.privateInPublic true
@[expose] public section

/-! The ordered auxiliary limits used in the marked correlation argument. -/

namespace ArtinMatthews

open Filter
open scoped Topology

noncomputable def markedCorrelationSieveExponent (c h : ℝ) : ℝ := c / (4 * h + 3)

/-- The squared inverse sieve exponent is absorbed by the exponential error. -/
theorem marked_correlation_sieve_error_tendsto (c : ℝ) :
    Tendsto (fun h : ℝ => Real.exp (-h) / (markedCorrelationSieveExponent c h) ^ 2)
      atTop (𝓝 0) := by
  have h₀ := Real.tendsto_exp_neg_atTop_nhds_zero
  have h₁ := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have h₂ := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2
  have hh := (((h₂.const_mul 16).add (h₁.const_mul 24)).add (h₀.const_mul 9)).div_const (c ^ 2)
  convert hh using 1
  · ext h
    simp only [markedCorrelationSieveExponent, div_pow, div_div_eq_mul_div, pow_one]
    ring
  · norm_num

/-- Only even depths are needed in the block-sieve application. -/
theorem marked_correlation_even_sieve_error_tendsto (c A : ℝ) :
    Tendsto (fun n : ℕ => A * Real.exp (-(2 * (n : ℝ))) /
      (markedCorrelationSieveExponent c (2 * n)) ^ 2) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => 2 * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  simpa only [Function.comp_apply, mul_zero, mul_div_assoc] using
    ((marked_correlation_sieve_error_tendsto c).comp hn).const_mul A

/-- An error controlled for each fixed even depth by arbitrarily many
arrays tends to zero. The array constant may depend arbitrarily on the
fixed depth; no uniformity in that depth is assumed. -/
theorem marked_ordered_auxiliary_limits (E : ℝ → ℝ) (c A : ℝ) (n₀ : ℕ)
    (hE : ∀ᶠ x : ℝ in atTop, 0 ≤ E x)
    (hbound : ∀ n ≥ n₀, ∃ D : ℝ, ∀ B : ℕ, 0 < B → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ x : ℝ in atTop, E x ≤
        A * Real.exp (-(2 * (n : ℝ))) / (markedCorrelationSieveExponent c (2 * n)) ^ 2 +
          D / Real.sqrt B + ε) :
    Tendsto E atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [hE] with x hx
    exact ha.trans_le hx
  · intro a ha
    have ha3 : 0 < a / 3 := by linarith
    have hh := ((marked_correlation_even_sieve_error_tendsto c A).eventually
      (gt_mem_nhds ha3)).and (eventually_ge_atTop n₀)
    obtain ⟨n, hnsmall, hn₀⟩ := hh.exists
    obtain ⟨D, hD⟩ := hbound n hn₀
    have hB := ((marked_deweighting_array_count_decay D).eventually
      (gt_mem_nhds ha3)).and (eventually_gt_atTop (0 : ℕ))
    obtain ⟨B, hBsmall, hBpos⟩ := hB.exists
    filter_upwards [hD B hBpos (a / 3) ha3] with x hx
    linarith

end ArtinMatthews
