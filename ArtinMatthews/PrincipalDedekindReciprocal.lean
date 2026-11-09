module

public import ArtinMatthews.VaryingKummerAnalyticMixedZetaZero
public import ArtinMatthews.VaryingKummerAnalyticDedekindEulerLog
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine pole-removed Dedekind function and its reciprocal. The
value at one is the actual class-number residue; the zeta continuation
itself retains its totalized meromorphic convention. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField Complex Set Filter
open scoped NumberField Classical Topology
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

def principalDedekindRegularized (s : ℂ) : ℂ := mixedDedekindEntireNumerator K s

theorem principalDedekindRegularized_entire :
    Differentiable ℂ (principalDedekindRegularized K) :=
  mixedDedekindEntireNumerator_entire K

theorem principalDedekindRegularized_one :
    principalDedekindRegularized K 1 = (dedekindZeta_residue K : ℂ) := by
  rw [principalDedekindRegularized, mixedDedekindEntireNumerator_eq_regularized K one_ne_zero,
    mixedRegularizedDedekindZeta_one]

theorem principalDedekindRegularized_one_ne_zero :
    principalDedekindRegularized K 1 ≠ 0 := by
  rw [principalDedekindRegularized_one]
  exact Complex.ofReal_ne_zero.mpr (dedekindZeta_residue_ne_zero K)

theorem principalDedekindRegularized_eq_zeta {s : ℂ} (hs : s ≠ 1) :
    principalDedekindRegularized K s = (s-1) * mixedDedekindZeta K s := by
  unfold principalDedekindRegularized mixedDedekindZeta
  exact (mul_div_cancel₀ _ (sub_ne_zero.mpr hs)).symm

theorem principalDedekindRegularized_eq_series {s : ℂ} (hs : 1 < s.re) :
    principalDedekindRegularized K s = (s-1) * dedekindZeta K s := by
  rw [principalDedekindRegularized_eq_zeta K (by intro h; simp [h] at hs),
    mixedDedekindZeta_eq K hs]

theorem principalDedekindRegularized_ne_zero_right {s : ℂ} (hs : 1 < s.re) :
    principalDedekindRegularized K s ≠ 0 := by
  rw [principalDedekindRegularized_eq_series K hs, ← exp_dedekindEulerLog_eq_dedekindZeta K hs]
  exact mul_ne_zero (sub_ne_zero.mpr (by intro h; simp [h] at hs)) (Complex.exp_ne_zero _)

def principalDedekindReciprocal (s : ℂ) : ℂ := (principalDedekindRegularized K s)⁻¹

theorem principalDedekindReciprocal_one :
    principalDedekindReciprocal K 1 = (dedekindZeta_residue K : ℂ)⁻¹ := by
  rw [principalDedekindReciprocal, principalDedekindRegularized_one]

theorem principalDedekindReciprocal_analyticAt {s : ℂ}
    (hs : principalDedekindRegularized K s ≠ 0) :
    AnalyticAt ℂ (principalDedekindReciprocal K) s :=
  ((principalDedekindRegularized_entire K).analyticAt s).inv hs

theorem principalDedekindReciprocal_analyticAt_one :
    AnalyticAt ℂ (principalDedekindReciprocal K) 1 :=
  principalDedekindReciprocal_analyticAt K (principalDedekindRegularized_one_ne_zero K)

theorem principalDedekindReciprocal_differentiableAt {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ (principalDedekindReciprocal K) s :=
  (principalDedekindReciprocal_analyticAt K
    (principalDedekindRegularized_ne_zero_right K hs)).differentiableAt

theorem principalDedekindReciprocal_eq_exp_neg_eulerLog {s : ℂ} (hs : 1 < s.re) :
    principalDedekindReciprocal K s = Complex.exp (-dedekindEulerLog K s) / (s-1) := by
  rw [principalDedekindReciprocal, principalDedekindRegularized_eq_series K hs,
    mul_inv_rev, ← exp_dedekindEulerLog_eq_dedekindZeta K hs, ← Complex.exp_neg]
  rfl

def principalDedekindReciprocalBound : ℝ :=
  4 * Real.exp ((Module.finrank ℚ K : ℝ) * dedekindEulerLogConstant)

theorem principalDedekindReciprocalBound_pos : 0 < principalDedekindReciprocalBound K := by
  unfold principalDedekindReciprocalBound
  positivity

theorem principalDedekindReciprocal_norm_le {s : ℂ} (hs : 5/4 ≤ s.re) :
    ‖principalDedekindReciprocal K s‖ ≤ principalDedekindReciprocalBound K := by
  have he : ‖Complex.exp (-dedekindEulerLog K s)‖ ≤
      Real.exp ((Module.finrank ℚ K : ℝ) * dedekindEulerLogConstant) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hr := Complex.re_le_norm (-dedekindEulerLog K s)
    simp only [Complex.neg_re, norm_neg] at hr
    exact hr.trans (dedekindEulerLog_norm_le K hs)
  have hd : (1/4 : ℝ) ≤ ‖s-1‖ := by
    have hr := Complex.re_le_norm (s-1)
    simp only [Complex.sub_re, Complex.one_re] at hr
    linarith
  rw [principalDedekindReciprocal_eq_exp_neg_eulerLog K (by linarith), norm_div]
  apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/4) hd)).mpr
  unfold principalDedekindReciprocalBound
  have hp := Real.exp_pos ((Module.finrank ℚ K : ℝ) * dedekindEulerLogConstant)
  nlinarith

/-- This identity includes the totalized value at one. It is the linear
factor that distinguishes the zeta reciprocal from the filled reciprocal. -/
theorem mixedDedekindZeta_inv_eq_regularized (s : ℂ) :
    (mixedDedekindZeta K s)⁻¹ = (s-1) * principalDedekindReciprocal K s := by
  simp only [mixedDedekindZeta, principalDedekindReciprocal,
    principalDedekindRegularized, div_eq_mul_inv, mul_inv_rev, inv_inv]

theorem mixedDedekindZeta_inv_analyticAt_one :
    AnalyticAt ℂ (fun s => (mixedDedekindZeta K s)⁻¹) 1 := by
  have h : (fun s => (mixedDedekindZeta K s)⁻¹) =
      fun s => (s-1) * principalDedekindReciprocal K s :=
    funext (mixedDedekindZeta_inv_eq_regularized K)
  rw [h]
  exact (analyticAt_id.sub analyticAt_const).mul (principalDedekindReciprocal_analyticAt_one K)

theorem mixedDedekindZeta_inv_one : (mixedDedekindZeta K 1)⁻¹ = 0 := by
  rw [mixedDedekindZeta_inv_eq_regularized]
  simp

theorem principalDedekindRegularized_logDeriv {s : ℂ} (hs : s ≠ 1)
    (hz : mixedDedekindZeta K s ≠ 0) :
    logDeriv (principalDedekindRegularized K) s =
      1/(s-1) + logDeriv (mixedDedekindZeta K) s := by
  have he : principalDedekindRegularized K =ᶠ[𝓝 s]
      (fun z : ℂ => (z-1) * mixedDedekindZeta K z) := by
    filter_upwards [isOpen_ne.mem_nhds hs] with z hz
    exact principalDedekindRegularized_eq_zeta K hz
  rw [(logDeriv_congr_nhds he).eq_of_nhds,
    logDeriv_fun_mul (f := fun z : ℂ => z-1) (g := mixedDedekindZeta K) s
      (sub_ne_zero.mpr hs) hz (differentiableAt_id.sub_const 1)
      (mixedDedekindZeta_analyticAt K hs).differentiableAt]
  congr 1
  rw [logDeriv_apply, ((hasDerivAt_id' s).sub_const 1).deriv]

end
end ArtinMatthews.VaryingKummerAnalytic
