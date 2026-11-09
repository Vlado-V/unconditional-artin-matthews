module

public import ArtinMatthews.IdealCharacterReproductionActual


set_option backward.privateInPublic true
@[expose] public section

/-! Source-scale consequences used by the rational approximation on
each occupied product dyad. -/
namespace ArtinMatthews
open Filter
open scoped Topology
noncomputable section

theorem idealSource_rational_scale (a c : ℝ) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ U V : ℝ,
      Real.exp (L^c)/4 ≤ U → Real.exp (L^c)/4 ≤ V → L^a ≤ 16*U*V := by
  have hfast := (rpow_mul_exp_neg_rpow_tendsto a hc (by norm_num : (0 : ℝ) < 1)).eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hfast, eventually_ge_atTop (0 : ℝ)] with L hfast hL0
  intro U V hU hV
  have hp := Real.exp_pos (L^c)
  have hL : L^a ≤ Real.exp (L^c) := by
    apply le_of_lt
    apply (div_lt_one hp).mp
    simpa only [neg_one_mul, Real.exp_neg, div_eq_mul_inv] using hfast
  have he : 1 ≤ Real.exp (L^c) := Real.one_le_exp (Real.rpow_nonneg hL0 c)
  have hUV := mul_le_mul hU hV (by positivity : 0 ≤ Real.exp (L^c)/4)
    (by linarith : 0 ≤ U)
  nlinarith

theorem idealSource_gram_log_bound (d : ℝ) (hd : 0 ≤ d) :
    ∀ᶠ L : ℝ in atTop, ∀ U V r : ℕ, 0 < U → 0 < V → 0 < r →
      Real.log (U : ℝ) ≤ L^(d+2) → Real.log (V : ℝ) ≤ L^(d+2) →
      (r : ℝ) ≤ 64*(U : ℝ)*(V : ℝ) → 1+Real.log (2*(r : ℝ)) ≤ L^(d+3) := by
  filter_upwards [eventually_ge_atTop (max 2 (3+Real.log 128))] with L hlarge
  have hL1 : 1 ≤ L := by have := (le_max_left _ _).trans hlarge; linarith
  have hL : 0 < L := zero_lt_one.trans_le hL1
  have hK : 3+Real.log 128 ≤ L := (le_max_right _ _).trans hlarge
  have hp : 1 ≤ L^(d+2) := Real.one_le_rpow hL1 (by linarith)
  intro U V r hU hV hr hlogU hlogV hrbound
  have hUr : (0 : ℝ) < U := by exact_mod_cast hU
  have hVr : (0 : ℝ) < V := by exact_mod_cast hV
  have hrr : (0 : ℝ) < r := by exact_mod_cast hr
  have hlog : Real.log (2*(r : ℝ)) ≤ Real.log 128+Real.log (U : ℝ)+Real.log (V : ℝ) := by
    have hh := Real.log_le_log (show 0 < 2*(r : ℝ) by positivity)
      (show 2*(r : ℝ) ≤ 128*(U : ℝ)*(V : ℝ) by linarith)
    rw [Real.log_mul (by positivity : (128 : ℝ)*(U : ℝ) ≠ 0) hVr.ne',
      Real.log_mul (by norm_num : (128 : ℝ) ≠ 0) hUr.ne'] at hh
    exact hh
  have hlog0 : 0 ≤ Real.log 128 := Real.log_nonneg (by norm_num)
  calc
    _ ≤ 1+Real.log 128+2*L^(d+2) := by linarith
    _ ≤ (3+Real.log 128)*L^(d+2) := by nlinarith
    _ ≤ L*L^(d+2) := mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hL.le _)
    _ = _ := by nth_rw 1 [← Real.rpow_one L]; rw [← Real.rpow_add hL]; congr 1; ring

theorem idealSource_log_width (H : ℝ) (hH : 1 ≤ H) :
    ∀ᶠ L : ℝ in atTop, 0 < L^(-H) ∧ Real.exp (L^(-H)) ≤ 2 := by
  filter_upwards [eventually_ge_atTop (max 2 (Real.log 2)⁻¹)] with L hlarge
  have hL1 : 1 ≤ L := by have := (le_max_left _ _).trans hlarge; linarith
  have hL : 0 < L := zero_lt_one.trans_le hL1
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbound : L^(-H) ≤ Real.log 2 := by
    calc
      _ ≤ L^(-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      _ = L⁻¹ := Real.rpow_neg_one _
      _ ≤ (Real.log 2)⁻¹⁻¹ := inv_anti₀ (inv_pos.mpr hlog) ((le_max_right _ _).trans hlarge)
      _ = _ := inv_inv _
  exact ⟨Real.rpow_pos_of_pos hL _, (Real.exp_le_exp.mpr hbound).trans_eq (Real.exp_log (by norm_num))⟩

end
end ArtinMatthews
