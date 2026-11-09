module

public import ArtinMatthews.SourceComplexMellinLogBound
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.VaryingKummerAnalytic
open MeasureTheory Set Filter
open scoped SchwartzMap Topology
noncomputable section

theorem sourceComplexMellin_integrand_hasDerivAt (f : ℂ → ℂ) (s z : ℂ) :
    HasDerivAt (fun w : ℂ => f z * sourceComplexMellinWeight w z)
      (sourceComplexMellinDerivativeIntegrand f s z) s := by
  have harg := (((hasDerivAt_id s).const_mul (2 : ℂ)).sub_const 2).mul_const (Real.log ‖z‖ : ℂ)
  have h := ((Complex.hasDerivAt_exp _).comp s harg).const_mul (f z)
  convert h using 1
  · rfl
  · simp only [sourceComplexMellinDerivativeIntegrand, sourceComplexMellinWeight, id_eq]
    ring

theorem sourceComplexMellin_integrand_measurable (f : 𝓢(ℂ, ℂ)) (s : ℂ) :
    Measurable (fun z : ℂ => f z * sourceComplexMellinWeight s z) :=
  f.continuous.measurable.mul (sourceComplexMellinWeight_measurable s)

theorem sourceComplexMellin_derivative_measurable (f : 𝓢(ℂ, ℂ)) (s : ℂ) :
    Measurable (sourceComplexMellinDerivativeIntegrand f s) := by
  exact (measurable_const.mul (Complex.continuous_ofReal.measurable.comp
    (Real.measurable_log.comp continuous_norm.measurable))).mul
    (sourceComplexMellin_integrand_measurable f s)

theorem sourceComplexMellin_hasDerivAt (f : 𝓢(ℂ, ℂ)) (s : ℂ) (hs : 0 < s.re) :
    HasDerivAt (sourceComplexMellin f)
      (∫ z : ℂ, sourceComplexMellinDerivativeIntegrand f s z ∂sourceComplexTraceMeasure) s := by
  let lo : ℝ := s.re / 2
  let hi : ℝ := 3 * s.re / 2
  have hlo : 0 < lo := by dsimp [lo]; positivity
  have hstrip : ∀ w ∈ Metric.ball s lo, lo ≤ w.re ∧ w.re ≤ hi := by
    intro w hw
    have hd := Metric.mem_ball.mp hw
    rw [dist_eq_norm] at hd
    have hr := (Complex.abs_re_le_norm (w - s)).trans hd.le
    rw [Complex.sub_re] at hr
    have hr' := abs_le.mp hr
    dsimp [lo, hi] at *
    constructor <;> linarith [hr'.1, hr'.2]
  have hb : Integrable (fun z : ℂ => (4 / lo) *
      sourceComplexMellinMajorant f (lo / 2) (hi + lo / 2) z) sourceComplexTraceMeasure :=
    (sourceComplexMellinMajorant_integrable f (lo / 2) (hi + lo / 2) (by positivity)).const_mul _
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := sourceComplexTraceMeasure) (F := fun w z => f z * sourceComplexMellinWeight w z)
    (F' := sourceComplexMellinDerivativeIntegrand f) (Metric.ball_mem_nhds s hlo)
    (Filter.Eventually.of_forall fun w => (sourceComplexMellin_integrand_measurable f w).aestronglyMeasurable)
    (sourceComplexMellin_integrable f s hs)
    (sourceComplexMellin_derivative_measurable f s).aestronglyMeasurable
    (by
      filter_upwards [sourceComplexTraceMeasure_ae_ne_zero] with z hz
      intro w hw
      exact sourceComplexMellin_derivative_norm_le f lo hi w z hlo
        (hstrip w hw).1 (hstrip w hw).2 hz)
    hb (Filter.Eventually.of_forall fun z w _ => sourceComplexMellin_integrand_hasDerivAt f w z)
  exact h.2

theorem sourceComplexMellin_analyticOnNhd (f : 𝓢(ℂ, ℂ)) :
    AnalyticOnNhd ℂ (sourceComplexMellin f) {s : ℂ | 0 < s.re} := by
  have h : DifferentiableOn ℂ (sourceComplexMellin f) {s : ℂ | 0 < s.re} := fun s hs =>
    (sourceComplexMellin_hasDerivAt f s hs).differentiableAt.differentiableWithinAt
  exact h.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

end
end ArtinMatthews.VaryingKummerAnalytic
