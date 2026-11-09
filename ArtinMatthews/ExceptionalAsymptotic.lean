module

public import ArtinMatthews.ProductGrowth
public import ArtinMatthews.DivisorBound
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics


set_option backward.privateInPublic true
@[expose] public section

/-!
# Negligibility of the final exceptional product

The primes above `x` dividing the short-exponent product with cutoff
`floor (2 x^ε)` are negligible relative to `x / log x` when `0 < ε < 1/2`.
This conclusion uses only the elementary product estimate, not the analytic
lower bound for simultaneous primitive roots.
-/

open Filter
open scoped Topology

namespace ArtinMatthews

/-- The product-exclusion bound for an arbitrary exponent cutoff. -/
theorem card_exceptional_primeFactorsAbove_mul_log_le
    {S : Finset ℤ} (hS : AdmissibleBases S) {m : ℕ} (hm : 1 ≤ m)
    {x : ℝ} (hx : 1 < x) :
    ((primeFactorsAbove (exceptionalProduct S m) x).card : ℝ) * Real.log x ≤
      productGrowthConstant S * (m : ℝ) ^ 2 :=
  (card_primeFactorsAbove_mul_log_le_log (exceptionalProduct_pos hS m) hx).trans
    (log_exceptionalProduct_le hS hm)

/-- Cardinality form of the product-exclusion bound. -/
theorem card_exceptional_primeFactorsAbove_le
    {S : Finset ℤ} (hS : AdmissibleBases S) {m : ℕ} (hm : 1 ≤ m)
    {x : ℝ} (hx : 1 < x) :
    ((primeFactorsAbove (exceptionalProduct S m) x).card : ℝ) ≤
      productGrowthConstant S * (m : ℝ) ^ 2 / Real.log x := by
  exact (le_div_iff₀ (Real.log_pos hx)).mpr
    (card_exceptional_primeFactorsAbove_mul_log_le hS hm hx)

/-- The exponent cutoff in the last product-exclusion step. -/
noncomputable def exceptionalExponentCutoff (ε x : ℝ) : ℕ :=
  ⌊2 * x ^ ε⌋₊

/-- Number of primes above `x` dividing the exceptional product at its cutoff. -/
noncomputable def exceptionalPrimeCount (S : Finset ℤ) (ε x : ℝ) : ℕ :=
  (primeFactorsAbove (exceptionalProduct S (exceptionalExponentCutoff ε x)) x).card

lemma exceptionalExponentCutoff_pos {ε x : ℝ} (hε : 0 ≤ ε) (hx : 1 ≤ x) :
    1 ≤ exceptionalExponentCutoff ε x := by
  apply (Nat.one_le_floor_iff _).mpr
  have hpow : 1 ≤ x ^ ε := Real.one_le_rpow hx hε
  linarith

lemma exceptionalExponentCutoff_sq_le {ε x : ℝ} (hx : 0 ≤ x) :
    (exceptionalExponentCutoff ε x : ℝ) ^ 2 ≤ 4 * x ^ (2 * ε) := by
  have hpow : 0 ≤ x ^ ε := Real.rpow_nonneg hx ε
  have hfloor : (exceptionalExponentCutoff ε x : ℝ) ≤ 2 * x ^ ε :=
    Nat.floor_le (by positivity)
  have hsquare : (exceptionalExponentCutoff ε x : ℝ) ^ 2 ≤ (2 * x ^ ε) ^ 2 := by
    gcongr
  have hrpow : x ^ (2 * ε) = (x ^ ε) ^ 2 := by
    simpa only [Nat.cast_ofNat, mul_comm] using (Real.rpow_mul_natCast hx ε 2)
  rw [hrpow]
  nlinarith

/-- An explicit power-saving bound for the exceptional count after normalization. -/
theorem exceptionalPrimeCount_normalized_le
    {S : Finset ℤ} (hS : AdmissibleBases S) {ε x : ℝ}
    (hε : 0 ≤ ε) (hx : 1 < x) :
    (exceptionalPrimeCount S ε x : ℝ) / (x / Real.log x) ≤
      4 * productGrowthConstant S * x ^ (2 * ε - 1) := by
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hC : 0 ≤ productGrowthConstant S := (productGrowthConstant_pos hS).le
  have hcount := card_exceptional_primeFactorsAbove_mul_log_le hS
    (exceptionalExponentCutoff_pos hε hx.le) hx
  change (exceptionalPrimeCount S ε x : ℝ) * Real.log x ≤
    productGrowthConstant S * (exceptionalExponentCutoff ε x : ℝ) ^ 2 at hcount
  calc
    (exceptionalPrimeCount S ε x : ℝ) / (x / Real.log x) =
        ((exceptionalPrimeCount S ε x : ℝ) * Real.log x) / x := by
      field_simp
    _ ≤ (productGrowthConstant S * (exceptionalExponentCutoff ε x : ℝ) ^ 2) / x :=
      div_le_div_of_nonneg_right hcount hx0.le
    _ ≤ (productGrowthConstant S * (4 * x ^ (2 * ε))) / x :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (exceptionalExponentCutoff_sq_le hx0.le) hC) hx0.le
    _ = 4 * productGrowthConstant S * x ^ (2 * ε - 1) := by
      rw [Real.rpow_sub_one hx0.ne']
      ring

/-- The normalized final exceptional count tends to zero. -/
theorem tendsto_exceptionalPrimeCount_div
    {S : Finset ℤ} (hS : AdmissibleBases S) {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    Tendsto (fun x : ℝ => (exceptionalPrimeCount S ε x : ℝ) / (x / Real.log x))
      atTop (𝓝 0) := by
  have hpower : Tendsto (fun x : ℝ => x ^ (2 * ε - 1)) atTop (𝓝 0) := by
    simpa only [neg_sub] using
      (tendsto_rpow_neg_atTop (show 0 < 1 - 2 * ε by linarith))
  have hbound : Tendsto (fun x : ℝ =>
      4 * productGrowthConstant S * x ^ (2 * ε - 1)) atTop (𝓝 0) := by
    simpa using hpower.const_mul (4 * productGrowthConstant S)
  apply squeeze_zero' _ _ hbound
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_nonneg (Nat.cast_nonneg _) (div_nonneg (by linarith) (Real.log_pos hx).le)
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact exceptionalPrimeCount_normalized_le hS hε.le hx

/-- The final exceptional-prime contribution is `o(x / log x)`. -/
theorem exceptionalPrimeCount_isLittleO
    {S : Finset ℤ} (hS : AdmissibleBases S) {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    (fun x : ℝ => (exceptionalPrimeCount S ε x : ℝ)) =o[atTop]
      (fun x : ℝ => x / Real.log x) := by
  apply Asymptotics.isLittleO_of_tendsto' _ (tendsto_exceptionalPrimeCount_div hS hε hεhalf)
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  intro hz
  have : 0 < x / Real.log x := div_pos (by linarith) (Real.log_pos hx)
  exact False.elim ((ne_of_gt this) hz)

end ArtinMatthews
