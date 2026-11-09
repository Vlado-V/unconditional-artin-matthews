module

public import ArtinMatthews.SourceComplexProductPairing


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.VaryingKummerAnalytic
open MeasureTheory
open scoped BigOperators FourierTransform SchwartzMap ContDiff
noncomputable section
variable {ι : Type*} [Fintype ι]

theorem sourceComplexProductTest_actual_mellin_integrable :
    Integrable (fun y : ι → ℂ => sourceComplexProductFourier sourceComplexProductTest y *
      (sourceComplexProductAbsoluteValue y ^ (1 / 6 : ℝ) /
        sourceComplexProductAbsoluteValue y : ℝ)) (sourceComplexProductMeasure ι) := by
  simp_rw [source_complex_product_one_sixth_density, Complex.ofReal_prod]
  exact sourceComplexProductTest_trace_mellin_integrable

theorem sourceComplexProductTest_actual_physical_mellin_integrable :
    Integrable (fun y : ι → ℂ => sourceComplexProductTest y *
      (sourceComplexProductAbsoluteValue y ^ (5 / 6 : ℝ) /
        sourceComplexProductAbsoluteValue y : ℝ)) (sourceComplexProductMeasure ι) := by
  simp_rw [source_complex_product_five_sixths_density, Complex.ofReal_prod]
  exact sourceComplexProductTest_physical_pairing_integrable

/-- The literal test required for the archimedean part of the physical probe.
All Fourier and Mellin integrals use the proved trace self-dual local measures. -/
theorem source_archimedean_probe_test_exists [Nonempty ι] :
    ∃ W : (ι → ℂ) → ℂ,
      ContDiff ℝ ∞ W ∧ HasCompactSupport W ∧
      tsupport W ⊆ {x | ∀ i, x i ≠ 0} ∧
      sourceComplexProductFourier W 0 = 0 ∧
      Integrable (fun y : ι → ℂ => sourceComplexProductFourier W y *
        (sourceComplexProductAbsoluteValue y ^ (1 / 6 : ℝ) /
          sourceComplexProductAbsoluteValue y : ℝ)) (sourceComplexProductMeasure ι) ∧
      (∫ y : ι → ℂ, sourceComplexProductFourier W y *
        (sourceComplexProductAbsoluteValue y ^ (1 / 6 : ℝ) /
          sourceComplexProductAbsoluteValue y : ℝ) ∂sourceComplexProductMeasure ι) ≠ 0 ∧
      Integrable (fun y : ι → ℂ => W y *
        (sourceComplexProductAbsoluteValue y ^ (5 / 6 : ℝ) /
          sourceComplexProductAbsoluteValue y : ℝ)) (sourceComplexProductMeasure ι) ∧
      (∫ y : ι → ℂ, W y *
        (sourceComplexProductAbsoluteValue y ^ (5 / 6 : ℝ) /
          sourceComplexProductAbsoluteValue y : ℝ) ∂sourceComplexProductMeasure ι) ≠ 0 := by
  exact ⟨sourceComplexProductTest, sourceComplexProductTest_smooth,
    sourceComplexProductTest_compact, sourceComplexProductTest_away_coordinate_zero,
    sourceComplexProductTest_fourier_zero, sourceComplexProductTest_actual_mellin_integrable,
    sourceComplexProductTest_actual_mellin_nonzero,
    sourceComplexProductTest_actual_physical_mellin_integrable,
    sourceComplexProductTest_actual_physical_mellin_nonzero⟩

end
end ArtinMatthews.VaryingKummerAnalytic
