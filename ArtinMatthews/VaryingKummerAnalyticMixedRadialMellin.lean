module

public import ArtinMatthews.VaryingKummerAnalyticMixedRadialJacobian


set_option backward.privateInPublic true
@[expose] public section

/-! The actual mixed-signature Gaussian Mellin integral. Its Gamma factors,
field norm, degree, and archimedean multiplicities are all explicit. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField MeasureTheory Set Filter
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open ArtinMatthews.ReusedArchMellin
open scoped NumberField nonZeroDivisors Classical BigOperators ENNReal
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def mixedRadialJacobian : ℝ :=
  (2 / (Module.finrank ℚ K : ℝ)) * ∏ w : InfinitePlace K, (InfinitePlace.mult w : ℝ)

theorem mixedRadialJacobian_pos : 0 < mixedRadialJacobian K := by
  apply mul_pos
  · exact div_pos (by norm_num) (Nat.cast_pos.mpr Module.finrank_pos)
  · exact Finset.prod_pos (fun _ _ => Nat.cast_pos.mpr InfinitePlace.mult_pos)

theorem map_mixedRadialLogCoordinates :
    Measure.map (fun p : ℝ × logSpace K => mixedRadialLogCoordinates K p.2 p.1) volume =
      ENNReal.ofReal (mixedRadialJacobian K) • (volume : Measure (InfinitePlace K → ℝ)) := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hfc : Measurable (fun p : ℝ × logSpace K =>
      f (mixedRadialLogCoordinates K p.2 p.1)) :=
    hf.comp (mixedRadialLogCoordinates_continuous K).measurable
  rw [lintegral_map hf (mixedRadialLogCoordinates_continuous K).measurable,
    lintegral_smul_measure, Measure.volume_eq_prod,
    lintegral_prod _ hfc.aemeasurable]
  exact lintegral_mixedRadialLogCoordinates K f hf

theorem integral_mixedRadialLogCoordinates (f : (InfinitePlace K → ℝ) → ℂ)
    (hf : StronglyMeasurable f) :
    (∫ p : ℝ × logSpace K, f (mixedRadialLogCoordinates K p.2 p.1)) =
      (mixedRadialJacobian K : ℂ) * ∫ x, f x := by
  rw [← integral_map (mixedRadialLogCoordinates_continuous K).measurable.aemeasurable
      hf.aestronglyMeasurable,
    map_mixedRadialLogCoordinates, integral_smul_measure,
    ENNReal.toReal_ofReal (mixedRadialJacobian_pos K).le, Complex.real_smul]

theorem mixedSeparatedGaussian_continuous (a : K) (s : ℂ) :
    Continuous (mixedSeparatedGaussian K a s) := by
  apply continuous_finsetProd
  intro w _
  exact (continuous_gaussianLogKernel _ _).comp (continuous_apply w)

theorem mixedLogRadialKernel_integrable {a : K} (ha : a ≠ 0)
    {s : ℂ} (hs : 0 < s.re) : Integrable (mixedLogRadialKernel K a s) := by
  have hI := mixedSeparatedGaussian_integrable K ha hs
  have hf := (mixedSeparatedGaussian_continuous K a s).stronglyMeasurable
  have hc := (mixedRadialLogCoordinates_continuous K).measurable
  have H : Integrable (fun p : ℝ × logSpace K =>
      mixedSeparatedGaussian K a s (mixedRadialLogCoordinates K p.2 p.1)) := by
    apply (integrable_map_measure hf.aestronglyMeasurable hc.aemeasurable).mp
    rw [map_mixedRadialLogCoordinates]
    exact hI.smul_measure ENNReal.ofReal_ne_top
  simpa only [mixedSeparatedGaussian_coordinates] using H

theorem mixedLogRadialKernel_integral {a : K} (ha : a ≠ 0)
    {s : ℂ} (hs : 0 < s.re) :
    (∫ p : ℝ × logSpace K, mixedLogRadialKernel K a s p) =
      (mixedRadialJacobian K : ℂ) * mixedGammaFactor K s *
        ((|(Algebra.norm ℚ a : ℝ)| : ℝ) : ℂ)^(-s) := by
  have h := integral_mixedRadialLogCoordinates K (mixedSeparatedGaussian K a s)
    (mixedSeparatedGaussian_continuous K a s).stronglyMeasurable
  simp only [mixedSeparatedGaussian_coordinates] at h
  rw [h, mixedSeparatedGaussian_integral K ha hs]
  ring

def mixedRadialKernel (a : K) (s : ℂ) (t : ℝ) (u : logSpace K) : ℂ :=
  (t : ℂ)^((Module.finrank ℚ K : ℂ)*s/2-1) *
    Complex.exp (-((Real.pi*t*mixedArchEnergy K a u : ℝ) : ℂ))

theorem mixedLogRadialKernel_eq_radial (a : K) (s : ℂ) (v : ℝ) (u : logSpace K) :
    mixedLogRadialKernel K a s (v,u) =
      Real.exp v • mixedRadialKernel K a s (Real.exp v) u := by
  rw [mixedRadialKernel, Complex.real_smul,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero v)),
    ← Complex.ofReal_log (Real.exp_pos v).le, Real.log_exp, Complex.ofReal_exp,
    ← Complex.exp_add, ← Complex.exp_add]
  unfold mixedLogRadialKernel
  congr 1
  push_cast
  ring

theorem mixedRadialIntegral_log (a : K) (s : ℂ) (v : ℝ) :
    (∫ u, mixedLogRadialKernel K a s (v,u)) =
      Real.exp v • ∫ u, mixedRadialKernel K a s (Real.exp v) u := by
  simp_rw [mixedLogRadialKernel_eq_radial]
  exact integral_smul _ _

theorem mixedRadialKernel_mellin {a : K} (ha : a ≠ 0) {s : ℂ} (hs : 0 < s.re) :
    (∫ t : ℝ in Ioi 0, ∫ u : logSpace K, mixedRadialKernel K a s t u) =
      (mixedRadialJacobian K : ℂ) * mixedGammaFactor K s *
        ((|(Algebra.norm ℚ a : ℝ)| : ℝ) : ℂ)^(-s) := by
  have H := integral_image_eq_integral_abs_deriv_smul
    (s := Set.univ) (f := Real.exp) (f' := Real.exp) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn (fun t => ∫ u, mixedRadialKernel K a s t u)
  simp only [Set.image_univ, Real.range_exp, abs_of_pos (Real.exp_pos _),
    ← mixedRadialIntegral_log, Measure.restrict_univ] at H
  rw [H]
  have HI := mixedLogRadialKernel_integrable K ha hs
  rw [Measure.volume_eq_prod] at HI
  rw [← integral_prod _ HI, ← Measure.volume_eq_prod]
  exact mixedLogRadialKernel_integral K ha hs

end
end ArtinMatthews.VaryingKummerAnalytic
