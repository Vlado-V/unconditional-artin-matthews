module

public import ArtinMatthews.CubicSieveMarkingEuler


set_option backward.privateInPublic true
@[expose] public section

/-! The literal marking-prime densities and their exclusion by the original
squarefree sieve divisor. -/

noncomputable section
namespace ArtinMatthews

open Finset
open scoped BigOperators

def cubicSieveMarkingPrimeFactor (p : ℕ) (s : ℝ) : ℝ :=
  (1 - cubicSieveEulerPower p s) ^ 2 / ((p : ℝ) - 1)

def cubicSieveRestrictedMarkingDensity (r p : ℕ) (s : ℝ) : ℝ :=
  if p ∣ r then 0 else cubicSieveMarkingPrimeFactor p s

def cubicSieveRestrictedMarkingTangent (r p : ℕ) : ℝ :=
  if p ∣ r then 0 else 2 * Real.log (p : ℝ) / (p : ℝ) ^ 2

theorem cubicSieve_markingPrimeFactor_one {p : ℕ} (hp : 1 < p) :
    cubicSieveMarkingPrimeFactor p 1 = 1 / (p : ℝ) - 1 / (p : ℝ) ^ 2 := by
  have hp₀ : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hp₁ : (p : ℝ) - 1 ≠ 0 := (sub_pos.mpr (by exact_mod_cast hp : (1 : ℝ) < p)).ne'
  rw [cubicSieveMarkingPrimeFactor, cubicSieve_eulerPower_one (by omega : 0 < p)]
  field_simp

theorem cubicSieve_markingPrimeFactor_hasDerivAt_one {p : ℕ} (hp : 1 < p) :
    HasDerivAt (cubicSieveMarkingPrimeFactor p) (2 * Real.log (p : ℝ) / (p : ℝ) ^ 2) 1 := by
  have hp₀ : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hp₁ : (p : ℝ) - 1 ≠ 0 := (sub_pos.mpr (by exact_mod_cast hp : (1 : ℝ) < p)).ne'
  have h := (((cubicSieve_eulerPower_hasDerivAt p 1).const_sub 1).pow 2).div_const ((p : ℝ) - 1)
  convert h using 1
  · rfl
  · rw [cubicSieve_eulerPower_one (by omega : 0 < p)]
    norm_num
    field_simp

theorem cubicSieve_restrictedMarkingDensity_hasDerivAt_one (r : ℕ) {p : ℕ} (hp : 1 < p) :
    HasDerivAt (cubicSieveRestrictedMarkingDensity r p) (cubicSieveRestrictedMarkingTangent r p) 1 := by
  change HasDerivAt (fun s => if p ∣ r then 0 else cubicSieveMarkingPrimeFactor p s)
    (if p ∣ r then 0 else 2 * Real.log (p : ℝ) / (p : ℝ) ^ 2) 1
  by_cases h : p ∣ r
  · simpa only [ite_eq_left h] using hasDerivAt_const (1 : ℝ) (0 : ℝ)
  · simpa only [ite_eq_right h] using cubicSieve_markingPrimeFactor_hasDerivAt_one hp

theorem cubicSieve_restrictedMarkingDensity_bounds (r : ℕ) {p : ℕ} (hp : p.Prime) :
    0 ≤ cubicSieveRestrictedMarkingDensity r p 1 ∧
      cubicSieveRestrictedMarkingDensity r p 1 ≤ 1 / (p : ℝ) := by
  have hp₂ : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp₀ : (0 : ℝ) < p := by linarith only [hp₂]
  have hu₀ := inv_nonneg.mpr hp₀.le
  have hu₁ : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith only [hp₂])
  unfold cubicSieveRestrictedMarkingDensity
  split_ifs
  · exact ⟨le_rfl, by positivity⟩
  · rw [cubicSieve_markingPrimeFactor_one hp.one_lt]
    simp only [one_div, ← inv_pow]
    exact ⟨by nlinarith only [mul_nonneg hu₀ (sub_nonneg.mpr hu₁)], sub_le_self _ (sq_nonneg _)⟩

theorem cubicSieve_restrictedMarkingDensity_distance (r : ℕ) {p : ℕ} (hp : p.Prime) :
    |cubicSieveRestrictedMarkingDensity r p 1 - 1 / (p : ℝ)| =
      if p ∣ r then 1 / (p : ℝ) else 1 / (p : ℝ) ^ 2 := by
  unfold cubicSieveRestrictedMarkingDensity
  by_cases h : p ∣ r
  · simp only [ite_eq_left h, zero_sub, abs_neg, abs_of_nonneg (by positivity : 0 ≤ 1 / (p : ℝ))]
  · rw [ite_eq_right h, cubicSieve_markingPrimeFactor_one hp.one_lt, ite_eq_right h]
    rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg (by positivity : 0 ≤ 1 / (p : ℝ) ^ 2)]

theorem cubicSieve_restrictedMarkingTangent_relative (r : ℕ) {p : ℕ} (hp : p.Prime) :
    |cubicSieveRestrictedMarkingTangent r p| ≤
      (4 * Real.log (p : ℝ) / (p : ℝ)) * cubicSieveRestrictedMarkingDensity r p 1 := by
  have hp₂ : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp₀ : (0 : ℝ) < p := by linarith only [hp₂]
  have hlog := Real.log_nonneg (by linarith only [hp₂] : (1 : ℝ) ≤ p)
  have hu₀ := inv_nonneg.mpr hp₀.le
  have hu₂ : (p : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [← one_div]
    exact one_div_le_one_div_of_le (by norm_num) hp₂
  unfold cubicSieveRestrictedMarkingTangent cubicSieveRestrictedMarkingDensity
  by_cases h : p ∣ r
  · simp only [ite_eq_left h, abs_zero, mul_zero, le_refl]
  · rw [ite_eq_right h, ite_eq_right h, cubicSieve_markingPrimeFactor_one hp.one_lt,
      abs_of_nonneg (by positivity : 0 ≤ 2 * Real.log (p : ℝ) / (p : ℝ) ^ 2)]
    simp only [div_eq_mul_inv, ← inv_pow]
    have h := mul_le_mul_of_nonneg_left
      (show 2 ≤ 4 * (1 - (p : ℝ)⁻¹) by linarith only [hu₂])
      (mul_nonneg hlog (sq_nonneg (p : ℝ)⁻¹))
    nlinarith only [h]

theorem cubicSieve_restrictedMarkingTangent_interval (r : ℕ) {p : ℕ} (hp : p.Prime)
    {y Z : ℝ} (hy : 0 < y) (hlo : y ≤ p) (hhi : (p : ℝ) ≤ Z) :
    |cubicSieveRestrictedMarkingTangent r p| ≤
      (4 * Real.log Z / y) * cubicSieveRestrictedMarkingDensity r p 1 := by
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlog := Real.log_nonneg (by exact_mod_cast hp.one_lt.le : (1 : ℝ) ≤ p)
  have hlogZ := Real.log_le_log hp₀ hhi
  apply (cubicSieve_restrictedMarkingTangent_relative r hp).trans
  apply mul_le_mul_of_nonneg_right _ (cubicSieve_restrictedMarkingDensity_bounds r hp).1
  exact div_le_div₀ (mul_nonneg (by norm_num) (hlog.trans hlogZ))
    (mul_le_mul_of_nonneg_left hlogZ (by norm_num)) hy hlo

end ArtinMatthews
