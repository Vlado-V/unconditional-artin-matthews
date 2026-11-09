module

public import ArtinMatthews.SourceProbeW1
public import ArtinMatthews.VaryingKummerAnalyticSmoothMellin


set_option backward.privateInPublic true
@[expose] public section

/-! Literal Mellin normalization, vertical estimates, and inversion for the probe weight. -/

namespace ArtinMatthews.SourcePhysical
open MeasureTheory Set
open ArtinMatthews.VaryingKummerAnalytic
noncomputable section

def sourceProbeW1Mellin : ℂ → ℂ := mellin sourceProbeW1Complex

theorem sourceProbeW1Mellin_eq_integral (s : ℂ) :
    sourceProbeW1Mellin s =
      ∫ t : ℝ in Ioi 0, sourceProbeW1Complex t * (t : ℂ) ^ s / (t : ℂ) := by
  rw [sourceProbeW1Mellin, smoothMellin_eq_integral]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt ht)), Complex.cpow_one, mul_div_assoc]

theorem sourceProbeW1Mellin_one : sourceProbeW1Mellin 1 = 1 := by
  rw [sourceProbeW1Mellin, smoothMellin_eq_integral]
  simp only [sub_self, Complex.cpow_zero, mul_one, sourceProbeW1Complex, integral_complex_ofReal,
    sourceProbeW1_integral_positiveLine, Complex.ofReal_one]

theorem sourceProbeW1Mellin_one_ne_zero : sourceProbeW1Mellin 1 ≠ 0 := by
  rw [sourceProbeW1Mellin_one]
  exact one_ne_zero

theorem sourceProbeW1Mellin_convergent (s : ℂ) : MellinConvergent sourceProbeW1Complex s :=
  smoothMellin_convergent _ sourceProbeW1Complex_compact sourceProbeW1Complex_positive_support
    sourceProbeW1Complex_contDiff.continuous s

theorem sourceProbeW1Mellin_entire : Differentiable ℂ sourceProbeW1Mellin :=
  smoothMellin_entire _ sourceProbeW1Complex_compact sourceProbeW1Complex_positive_support
    sourceProbeW1Complex_contDiff.continuous

theorem sourceProbeW1Mellin_strip_decay (lo hi : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, lo ≤ s.re → s.re ≤ hi →
      (1 + |s.im|) ^ n * ‖sourceProbeW1Mellin s‖ ≤ C :=
  smoothMellin_strip_decay _ sourceProbeW1Complex_compact sourceProbeW1Complex_positive_support
    sourceProbeW1Complex_contDiff lo hi n

theorem sourceProbeW1Mellin_continuous_vertical (σ : ℝ) :
    Continuous (fun t : ℝ => sourceProbeW1Mellin ((σ : ℂ) + t * Complex.I)) :=
  sourceProbeW1Mellin_entire.continuous.comp (by fun_prop)

theorem sourceProbeW1Mellin_measurable_vertical (σ : ℝ) :
    Measurable (fun t : ℝ => sourceProbeW1Mellin ((σ : ℂ) + t * Complex.I)) :=
  (sourceProbeW1Mellin_continuous_vertical σ).measurable

theorem sourceProbeW1Mellin_verticalIntegrable (σ : ℝ) :
    Complex.VerticalIntegrable sourceProbeW1Mellin σ :=
  smoothMellin_verticalIntegrable _ sourceProbeW1Complex_compact sourceProbeW1Complex_positive_support
    sourceProbeW1Complex_contDiff σ

theorem sourceProbeW1MellinInv_integrable (σ : ℝ) {x : ℝ} (hx : 0 < x) :
    Integrable (fun t : ℝ => (x : ℂ) ^ (-((σ : ℂ) + t * Complex.I)) *
      sourceProbeW1Mellin ((σ : ℂ) + t * Complex.I)) := by
  let : NeZero (x : ℂ) := ⟨Complex.ofReal_ne_zero.mpr hx.ne'⟩
  have hc : Continuous (fun t : ℝ => (x : ℂ) ^ (-((σ : ℂ) + t * Complex.I))) :=
    (continuous_const_cpow (x : ℂ)).comp (by fun_prop)
  have hi : Integrable (fun t : ℝ => sourceProbeW1Mellin ((σ : ℂ) + t * Complex.I)) :=
    sourceProbeW1Mellin_verticalIntegrable σ
  apply (hi.norm.const_mul (x ^ (-σ))).mono'
    (hc.mul (sourceProbeW1Mellin_continuous_vertical σ)).aestronglyMeasurable
  filter_upwards with t
  simp [Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.mul_re]

theorem sourceProbeW1_mellinInv (σ : ℝ) {x : ℝ} (hx : 0 < x) :
    mellinInv σ sourceProbeW1Mellin x = sourceProbeW1Complex x :=
  smoothMellin_inversion _ sourceProbeW1Complex_compact sourceProbeW1Complex_positive_support
    sourceProbeW1Complex_contDiff σ hx

theorem sourceProbeW1_eq_verticalIntegral (σ : ℝ) {x : ℝ} (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ, (x : ℂ) ^ (-((σ : ℂ) + t * Complex.I)) *
        sourceProbeW1Mellin ((σ : ℂ) + t * Complex.I)) = sourceProbeW1Complex x :=
  smoothMellin_inversion_integral _ sourceProbeW1Complex_compact sourceProbeW1Complex_positive_support
    sourceProbeW1Complex_contDiff σ hx

end
end ArtinMatthews.SourcePhysical
