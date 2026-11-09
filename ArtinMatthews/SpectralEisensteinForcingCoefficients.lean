module

public import ArtinMatthews.SpectralEisensteinVerticalCutoff


set_option backward.privateInPublic true
@[expose] public section

/-! Explicit fixed compact coefficients of the genuine cutoff forcing.
This separates its parameter dependence without asserting continuation. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace ArtinMatthews

theorem eisensteinVerticalCutoffMode_deriv (s : ℂ) {t : ℝ} (ht : 0 < t) :
    deriv (eisensteinVerticalCutoffMode s) t=
      ((deriv eisensteinHeightCutoff t:ℝ):ℂ)*(t:ℂ)^s+
        (eisensteinHeightCutoff t:ℂ)*(s*(t:ℂ)^(s-1)) := by
  have hχ : HasDerivAt eisensteinHeightCutoff (deriv eisensteinHeightCutoff t) t :=
    (eisensteinHeightCutoff_contDiff.differentiable (by simp)).differentiableAt.hasDerivAt
  exact (hχ.ofReal_comp.mul (eisensteinPositivePower_hasDerivAt s t ht)).deriv

theorem eisensteinVerticalCutoffMode_second_explicit (s : ℂ) {t : ℝ} (ht : 0 < t) :
    deriv (deriv (eisensteinVerticalCutoffMode s)) t=
      ((deriv (deriv eisensteinHeightCutoff) t:ℝ):ℂ)*(t:ℂ)^s+
        2*((deriv eisensteinHeightCutoff t:ℝ):ℂ)*s*(t:ℂ)^(s-1)+
        (eisensteinHeightCutoff t:ℂ)*s*(s-1)*(t:ℂ)^(s-2) := by
  have hχ : HasDerivAt eisensteinHeightCutoff (deriv eisensteinHeightCutoff t) t :=
    (eisensteinHeightCutoff_contDiff.differentiable (by simp)).differentiableAt.hasDerivAt
  have hχ' : HasDerivAt (deriv eisensteinHeightCutoff) (deriv (deriv eisensteinHeightCutoff) t) t :=
    ((contDiff_infty_iff_deriv.mp eisensteinHeightCutoff_contDiff).2.differentiable (by simp)).differentiableAt.hasDerivAt
  have he : deriv (eisensteinVerticalCutoffMode s) =ᶠ[𝓝 t]
      fun u => ((deriv eisensteinHeightCutoff u:ℝ):ℂ)*(u:ℂ)^s+
        (eisensteinHeightCutoff u:ℂ)*(s*(u:ℂ)^(s-1)) := by
    filter_upwards [eventually_gt_nhds ht] with u hu
    exact eisensteinVerticalCutoffMode_deriv s hu
  rw [he.deriv_eq]
  have h1 := hχ'.ofReal_comp.mul (eisensteinPositivePower_hasDerivAt s t ht)
  have h2 := hχ.ofReal_comp.mul ((eisensteinPositivePower_hasDerivAt (s-1) t ht).const_mul s)
  have h := (h1.add h2).deriv
  rw [show s-1-1=s-2 by ring] at h
  convert h using 1
  ring

def eisensteinForcingCoefficient0 (t : ℝ) : ℂ :=
  -((t:ℂ)^2)*((deriv (deriv eisensteinHeightCutoff) t:ℝ):ℂ)

def eisensteinForcingCoefficient1 (t : ℝ) : ℂ :=
  -2*(t:ℂ)*((deriv eisensteinHeightCutoff t:ℝ):ℂ)

theorem eisensteinVerticalCutoffError_explicit (s : ℂ) (t : ℝ) :
    eisensteinVerticalCutoffError s t=
      (eisensteinForcingCoefficient0 t+s*eisensteinForcingCoefficient1 t)*(t:ℂ)^s := by
  by_cases ht : 0 < t
  · rw [eisensteinVerticalCutoffError,eisensteinVerticalCutoffMode_second_explicit s ht,
      eisensteinVerticalCutoffMode,Complex.cpow_sub s 1 (Complex.ofReal_ne_zero.mpr ht.ne'),
      Complex.cpow_one,Complex.cpow_sub s 2 (Complex.ofReal_ne_zero.mpr ht.ne'),Complex.cpow_two]
    unfold eisensteinForcingCoefficient0 eisensteinForcingCoefficient1
    field_simp [Complex.ofReal_ne_zero.mpr ht.ne']
    ring
  · have hl : t < 1 := by linarith
    rw [eisensteinVerticalCutoffError_zero s (Or.inl hl),eisensteinForcingCoefficient0,
      eisensteinForcingCoefficient1,eisensteinHeightCutoff_deriv_zero (Or.inl hl),
      eisensteinHeightCutoff_second_zero (Or.inl hl)]
    simp

theorem eisensteinForcingCoefficient0_smooth : ContDiff ℝ ∞ eisensteinForcingCoefficient0 := by
  have h1 := (contDiff_infty_iff_deriv.mp eisensteinHeightCutoff_contDiff).2
  have h2 := (contDiff_infty_iff_deriv.mp h1).2
  exact (Complex.ofRealCLM.contDiff.pow 2).neg.mul (Complex.ofRealCLM.contDiff.comp h2)

theorem eisensteinForcingCoefficient1_smooth : ContDiff ℝ ∞ eisensteinForcingCoefficient1 :=
  (contDiff_const.mul Complex.ofRealCLM.contDiff).mul
    (Complex.ofRealCLM.contDiff.comp (contDiff_infty_iff_deriv.mp eisensteinHeightCutoff_contDiff).2)

theorem eisensteinForcingCoefficient0_zero {t : ℝ} (ht : t < 1 ∨ 2 < t) :
    eisensteinForcingCoefficient0 t=0 := by
  simp only [eisensteinForcingCoefficient0,eisensteinHeightCutoff_second_zero ht,Complex.ofReal_zero,mul_zero]

theorem eisensteinForcingCoefficient1_zero {t : ℝ} (ht : t < 1 ∨ 2 < t) :
    eisensteinForcingCoefficient1 t=0 := by
  simp only [eisensteinForcingCoefficient1,eisensteinHeightCutoff_deriv_zero ht,Complex.ofReal_zero,mul_zero]

theorem eisensteinForcingCoefficient0_support : tsupport eisensteinForcingCoefficient0 ⊆ Icc (1:ℝ) 2 := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  by_contra hn
  exact ht (eisensteinForcingCoefficient0_zero (by simpa only [mem_Icc,not_and_or,not_le] using hn))

theorem eisensteinForcingCoefficient1_support : tsupport eisensteinForcingCoefficient1 ⊆ Icc (1:ℝ) 2 := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  by_contra hn
  exact ht (eisensteinForcingCoefficient1_zero (by simpa only [mem_Icc,not_and_or,not_le] using hn))

end ArtinMatthews
