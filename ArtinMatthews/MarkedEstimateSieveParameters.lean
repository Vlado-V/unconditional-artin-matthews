module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-!
# Adapting the proved block sieve's constants

The available finite sieve has level `V ^ (12 * (m + 1))` and relative
error `exp (-m/2)`. Taking the sieve exponent to be `c₀/(24(m+1))`
places the level at `x^(c₀/2)`, strictly below the progression level
`x^c₀`. Its error divided by the sieve exponent still tends to zero.
This supplies the parameter adaptation needed for the manuscript's
successive limits; it asserts no progression remainder estimate.
-/

namespace ArtinMatthews

noncomputable def markedSieveExponent (c₀ : ℝ) (m : ℕ) : ℝ :=
  c₀ / (24 * ((m : ℝ) + 1))

theorem markedSieveExponent_pos {c₀ : ℝ} (hc : 0 < c₀) (m : ℕ) :
    0 < markedSieveExponent c₀ m := by
  unfold markedSieveExponent
  positivity

/-- The logarithmic divisor level leaves a factor of two of spare room. -/
theorem markedSieveExponent_level (c₀ : ℝ) (m : ℕ) :
    (12 * ((m : ℝ) + 1)) * markedSieveExponent c₀ m = c₀ / 2 := by
  unfold markedSieveExponent
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- The loss `1/γ` from the sieve density does not obstruct the final
limit when `γ = c₀/(24(m+1))`. -/
theorem markedSieve_error_tendsto (c₀ : ℝ) :
    Filter.Tendsto
      (fun m : ℕ => Real.exp (-(m : ℝ) / 2) / markedSieveExponent c₀ m)
      Filter.atTop (nhds 0) := by
  have hscale : Filter.Tendsto (fun m : ℕ => (m : ℝ) / 2) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num)
  have h₀ := Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale
  have h₁ := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hscale
  have hsum := ((h₁.const_mul 2).add h₀).const_mul (24 / c₀)
  convert hsum using 1
  · ext m
    simp only [Function.comp_apply, pow_one]
    unfold markedSieveExponent
    rw [div_div_eq_mul_div]
    ring
  · norm_num

end ArtinMatthews
