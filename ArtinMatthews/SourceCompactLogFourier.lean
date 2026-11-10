module

public import Mathlib.Analysis.Fourier.AddCircle

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Real.Pi.Bounds


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open Function Set MeasureTheory
open scoped FourierTransform ContDiff Interval
noncomputable section

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- The normalized coefficient of the periodic extension from one log period. -/
def sourceLogPeriodCoeff (f : ℝ → ℂ) (j : ℤ) : ℂ :=
  fourierCoeff (T := 1) (AddCircle.liftIoc 1 0 f) j

theorem sourceLogPeriodCoeff_eq_fourier {f : ℝ → ℂ} (hs : tsupport f ⊆ Ioo 0 1) (j : ℤ) :
    sourceLogPeriodCoeff f j = 𝓕 f (j : ℝ) := by
  rw [sourceLogPeriodCoeff, fourierCoeff_eq_intervalIntegral _ j 0, div_one, one_smul, zero_add,
    intervalIntegral.integral_of_le zero_le_one, Real.fourier_real_eq_integral_exp_smul]
  have hzero (t : ℝ) (ht : t ∉ Ioc (0 : ℝ) 1) : f t = 0 :=
    notMem_support.mp fun h => ht (Ioo_subset_Ioc_self (hs (subset_tsupport f h)))
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioc (0 : ℝ) 1)
    (f := fun t => Complex.exp (↑(-2 * Real.pi * t * (j : ℝ)) * Complex.I) • f t)
    (fun t ht => by rw [hzero t ht, smul_zero])]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  change fourier (-j) (t : UnitAddCircle) • AddCircle.liftIoc 1 0 f (t : UnitAddCircle) = _
  rw [AddCircle.liftIoc_zero_coe_apply ht, fourier_coe_apply]
  congr 2
  push_cast
  ring

theorem sourceLogPeriodCoeff_hasSum {f : ℝ → ℂ} (hf : Continuous f)
    (hs : tsupport f ⊆ Ioo 0 1) (hcoeff : Summable (sourceLogPeriodCoeff f))
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    HasSum (fun j : ℤ => sourceLogPeriodCoeff f j * fourier j (t : UnitAddCircle)) (f t) := by
  have h0 : f 0 = 0 := notMem_support.mp fun h => (hs (subset_tsupport f h)).1.false
  have h1 : f 1 = 0 := notMem_support.mp fun h => (hs (subset_tsupport f h)).2.false
  let p : C(UnitAddCircle, ℂ) := ⟨AddCircle.liftIoc 1 0 f,
    AddCircle.liftIoc_zero_continuous (h0.trans h1.symm) hf.continuousOn⟩
  have hp : p (t : UnitAddCircle) = f t := by
    change AddCircle.liftIoc 1 0 f (t : UnitAddCircle) = f t
    rcases ht.1.eq_or_lt with he | hpos
    · subst t
      rw [← AddCircle.coe_add_period 1 0, zero_add,
        AddCircle.liftIoc_zero_coe_apply (show (1 : ℝ) ∈ Ioc 0 1 from ⟨zero_lt_one, le_rfl⟩), h0, h1]
    · exact AddCircle.liftIoc_zero_coe_apply ⟨hpos, ht.2⟩
  rw [← hp]
  exact has_pointwise_sum_fourier_series_of_summable (f := p) hcoeff _

private theorem fourier_norm_le_of_unit_support {f : ℝ → ℂ}
    (hs : tsupport f ⊆ Ioo 0 1) {C : ℝ} (hC : ∀ t ∈ Icc (0 : ℝ) 1, ‖f t‖ ≤ C)
    (x : ℝ) : ‖𝓕 f x‖ ≤ C := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hzero (t : ℝ) (ht : t ∉ Ioc (0 : ℝ) 1) : f t = 0 :=
    notMem_support.mp fun h => ht (Ioo_subset_Ioc_self (hs (subset_tsupport f h)))
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioc (0 : ℝ) 1)
    (fun t ht => by rw [hzero t ht, smul_zero]), ← intervalIntegral.integral_of_le zero_le_one]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t => Complex.exp (↑(-2 * Real.pi * t * x) * Complex.I) • f t)
    (a := 0) (b := 1) (C := C) (fun t ht => by
      rw [uIoc_of_le zero_le_one] at ht
      rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
      exact hC t (Ioc_subset_Icc_self ht))
  simpa using h

/-- A common summable majorant profile, with its genuine zero-mode contribution. -/
def sourceLogFrequencyDecay (j : ℤ) : ℝ :=
  (if j = 0 then 1 else 0) + |(j : ℝ)| ^ (-(2 : ℝ))

theorem sourceLogFrequencyDecay_summable : Summable sourceLogFrequencyDecay :=
  (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable.add (Real.summable_abs_int_rpow (by norm_num))

theorem sourceLogFrequencyDecay_nonneg (j : ℤ) : 0 ≤ sourceLogFrequencyDecay j := by
  unfold sourceLogFrequencyDecay
  apply add_nonneg
  · by_cases hj : j = 0 <;> simp [hj]
  · exact Real.rpow_nonneg (abs_nonneg _) _

/-- Two actual integrations by parts give a uniform coefficient bound from log derivatives. -/
theorem sourceLogPeriodCoeff_bound {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hs : tsupport f ⊆ Ioo 0 1) {C : ℝ}
    (h0 : ∀ t ∈ Icc (0 : ℝ) 1, ‖f t‖ ≤ C)
    (h2 : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv (deriv f) t‖ ≤ C) (j : ℤ) :
    ‖sourceLogPeriodCoeff f j‖ ≤ C * sourceLogFrequencyDecay j := by
  rw [sourceLogPeriodCoeff_eq_fourier hs]
  by_cases hj : j = 0
  · subst j
    simpa [sourceLogFrequencyDecay] using fourier_norm_le_of_unit_support hs h0 0
  have hs' : tsupport (deriv f) ⊆ Ioo 0 1 := tsupport_deriv_subset.trans hs
  have hs'' : tsupport (deriv (deriv f)) ⊆ Ioo 0 1 := tsupport_deriv_subset.trans hs'
  have hf' : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  have hf'' : ContDiff ℝ ∞ (deriv (deriv f)) := (contDiff_infty_iff_deriv.mp hf').2
  have hI : HasCompactSupport f := isCompact_Icc.of_isClosed_subset isClosed_closure
    (hs.trans Ioo_subset_Icc_self)
  have hI₀ : Integrable f := hf.continuous.integrable_of_hasCompactSupport hI
  have hI₁ : Integrable (deriv f) := hf'.continuous.integrable_of_hasCompactSupport hI.deriv
  have hI₂ : Integrable (deriv (deriv f)) := hf''.continuous.integrable_of_hasCompactSupport hI.deriv.deriv
  have hFT : 𝓕 (deriv (deriv f)) (j : ℝ) =
      ((2 * (Real.pi : ℂ) * Complex.I * (j : ℂ)) ^ 2) * 𝓕 f (j : ℝ) := by
    rw [Real.fourier_deriv hI₁ (hf'.differentiable (by simp)) hI₂,
      Real.fourier_deriv hI₀ (hf.differentiable (by simp)) hI₁]
    simp only [smul_eq_mul, Complex.ofReal_intCast, pow_two, mul_assoc]
  have hfac : ‖(2 * (Real.pi : ℂ) * Complex.I * (j : ℂ))‖ = 2 * Real.pi * |(j : ℝ)| := by
    rw [← Complex.ofReal_intCast]
    simp only [norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, Complex.norm_I, mul_one]
  have hmain : (2 * Real.pi * |(j : ℝ)|)^2 * ‖𝓕 f (j : ℝ)‖ ≤ C := by
    simpa only [hFT, norm_mul, norm_pow, hfac] using
      fourier_norm_le_of_unit_support hs'' h2 (j : ℝ)
  have habs : 0 < |(j : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hj)
  have hfac₁ : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hle : |(j : ℝ)| ≤ 2 * Real.pi * |(j : ℝ)| := by
    simpa using mul_le_mul_of_nonneg_right hfac₁ habs.le
  have hsq : |(j : ℝ)| ^ 2 * ‖𝓕 f (j : ℝ)‖ ≤ C :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ habs.le hle 2) (norm_nonneg _)).trans hmain
  simp only [sourceLogFrequencyDecay, ite_eq_right hj, zero_add,
    Real.rpow_neg habs.le, Real.rpow_ofNat, ← div_eq_mul_inv]
  exact (le_div_iff₀ (pow_pos habs 2)).mpr (by simpa only [mul_comm] using hsq)

end
end ArtinMatthews.SourcePhysical
