module

public import ArtinMatthews.SourceComplexMellinHolomorphic
public import ArtinMatthews.SourceComplexMellinScale
public import ArtinMatthews.SourceComplexMellinSchwartzScale
public import ArtinMatthews.SourceComplexMellinRadialMajorant
public import Mathlib.Analysis.Complex.RealDeriv


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.VaryingKummerAnalytic
open MeasureTheory Set Filter
open scoped SchwartzMap Topology
noncomputable section

theorem sourceComplexMellin_dilation_integrand_hasDerivAt
    (f : 𝓢(ℂ, ℂ)) (s z : ℂ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => f (Real.exp u • z) * sourceComplexMellinWeight s z)
      (sourceComplexEulerSchwartz f (Real.exp t • z) * sourceComplexMellinWeight s z) t := by
  have h₁ := (Real.hasDerivAt_exp t).smul_const z
  have h₂ := (f.differentiable (Real.exp t • z)).hasFDerivAt.comp_hasDerivAt t h₁
  simpa only [Function.comp_apply, sourceComplexEulerSchwartz_apply] using
    h₂.mul_const (sourceComplexMellinWeight s z)

theorem sourceComplexMellin_dilation_hasDerivAt
    (f : 𝓢(ℂ, ℂ)) (s : ℂ) (hs : 0 < s.re) :
    HasDerivAt (fun t : ℝ => sourceComplexMellin (fun z => f (Real.exp t • z)) s)
      (sourceComplexMellin (sourceComplexEulerSchwartz f) s) 0 := by
  obtain ⟨C, hC, hdecay⟩ := sourceComplexSchwartz_exp_smul_norm_le
    (sourceComplexEulerSchwartz f) (sourceComplexMellinRadialPower s.re)
  have hmeas (g : 𝓢(ℂ, ℂ)) (t : ℝ) :
      Measurable (fun z : ℂ => g (Real.exp t • z) * sourceComplexMellinWeight s z) :=
    (g.continuous.comp (show Continuous (fun z : ℂ => Real.exp t • z) from
      (continuous_id : Continuous (id : ℂ → ℂ)).const_smul (Real.exp t))).measurable.mul
      (sourceComplexMellinWeight_measurable s)
  have hint : Integrable (fun z : ℂ => f (Real.exp 0 • z) * sourceComplexMellinWeight s z)
      sourceComplexTraceMeasure := by
    simpa only [Real.exp_zero, one_smul] using sourceComplexMellin_integrable f s hs
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := sourceComplexTraceMeasure)
    (F := fun (t : ℝ) (z : ℂ) => f (Real.exp t • z) * sourceComplexMellinWeight s z)
    (F' := fun t z => sourceComplexEulerSchwartz f (Real.exp t • z) *
      sourceComplexMellinWeight s z)
    (bound := fun z => C * sourceComplexMellinRadialMajorant s.re z)
    (s := Ioi (-1 : ℝ)) (Ioi_mem_nhds (by norm_num))
    (Filter.Eventually.of_forall fun t => (hmeas f t).aestronglyMeasurable)
    hint ((hmeas (sourceComplexEulerSchwartz f) 0).aestronglyMeasurable)
    (by
      filter_upwards [sourceComplexTraceMeasure_ae_ne_zero] with z hz
      intro t ht
      rw [norm_mul, sourceComplexMellinWeight_norm s z hz,
        sourceComplexMellinRadialMajorant, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hdecay t (le_of_lt ht) z) (by positivity))
    ((sourceComplexMellinRadialMajorant_integrable s.re hs).const_mul C)
    (Filter.Eventually.of_forall fun z t _ => sourceComplexMellin_dilation_integrand_hasDerivAt f s z t)
  simpa only [Real.exp_zero, one_smul, sourceComplexMellin] using h.2

/-- Logarithmic integration by parts, derived from genuine dominated dilation and its exact law. -/
theorem sourceComplexMellin_euler (f : 𝓢(ℂ, ℂ)) (s : ℂ) (hs : 0 < s.re) :
    sourceComplexMellin (sourceComplexEulerSchwartz f) s = -(2 * s) * sourceComplexMellin f s := by
  have h := sourceComplexMellin_dilation_hasDerivAt f s hs
  simp only [sourceComplexMellin_exp_smul] at h
  have h₂ := (((hasDerivAt_id (0 : ℂ)).const_mul (-(2 * s))).cexp).mul_const
    (sourceComplexMellin f s)
  have hc : HasDerivAt (fun w : ℂ => Complex.exp (-(2 * s) * w) * sourceComplexMellin f s)
      (-(2 * s) * sourceComplexMellin f s) (0 : ℂ) := by
    simpa only [id_eq, mul_zero, Complex.exp_zero, one_mul, mul_one] using h₂
  have h₃ : HasDerivAt
      (fun t : ℝ => Complex.exp (-(2 * s) * (t : ℂ)) * sourceComplexMellin f s)
      (-(2 * s) * sourceComplexMellin f s) 0 := by
    have hzero : HasDerivAt (fun w : ℂ => Complex.exp (-(2 * s) * w) * sourceComplexMellin f s)
        (-(2 * s) * sourceComplexMellin f s) ((0 : ℝ) : ℂ) := by
      simpa only [Complex.ofReal_zero] using hc
    exact hzero.comp_ofReal
  exact h.unique h₃

end
end ArtinMatthews.VaryingKummerAnalytic
