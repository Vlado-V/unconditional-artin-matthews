module

public import ArtinMatthews.CuspAverageProjectionIntegral


set_option backward.privateInPublic true
@[expose] public section

/-! Actual horizontal averaging on the unnormalized hyperbolic cusp strip. -/
noncomputable section
namespace ArtinMatthews
open MeasureTheory Set
open scoped ENNReal InnerProduct

/-- The bounded orthogonal projection agrees almost everywhere with the
literal normalized horizontal integral. -/
theorem cuspAverageProjection_ae_representative (w Y : ℝ) (hw : 0 < w)
    (f : CuspStripL2 w Y) :
    (cuspAverageProjection w Y f : ℝ × ℝ → ℂ)
      =ᵐ[cuspStripMeasure w Y] cuspAverageRepresentative w f := by
  let hmp : MeasurePreserving Prod.snd (cuspStripMeasure w Y)
      ((cuspHorizontalMeasure w univ) • cuspVerticalMeasure Y) :=
    ⟨measurable_snd, Measure.map_snd_prod⟩
  have hmean := Measure.ae_smul_measure
    (cuspVerticalAdjoint_ae_horizontalMean w Y hw f) (cuspHorizontalMeasure w univ)
  exact (Lp.coeFn_compMeasurePreserving _ hmp).trans
    (hmp.quasiMeasurePreserving.ae_eq_comp hmean)

/-- Subtracting the projection has exactly the pointwise mean-zero
representative already used in the smooth cusp-tail estimate. -/
theorem cuspMeanZeroL2_ae_representative (w Y : ℝ) (hw : 0 < w)
    (f : CuspStripL2 w Y) :
    ((f - cuspAverageProjection w Y f : CuspStripL2 w Y) : ℝ × ℝ → ℂ)
      =ᵐ[cuspStripMeasure w Y] cuspMeanZeroRepresentative w f := by
  filter_upwards [Lp.coeFn_sub f (cuspAverageProjection w Y f),
    cuspAverageProjection_ae_representative w Y hw f] with z hsub havg
  simpa only [Pi.sub_apply, cuspMeanZeroRepresentative, havg] using hsub

theorem cuspAverageProjection_eq_zero_iff (w Y : ℝ) (hw : 0 < w)
    (f : CuspStripL2 w Y) :
    cuspAverageProjection w Y f = 0 ↔
      cuspHorizontalMean w f =ᵐ[cuspVerticalMeasure Y] 0 := by
  let U := cuspVerticalPullback w Y
  have hkernel : cuspAverageProjection w Y f = 0 ↔
      U.toContinuousLinearMap.adjoint f = 0 := by
    change U (U.toContinuousLinearMap.adjoint f) = 0 ↔ _
    rw [← U.map_zero]
    exact U.injective.eq_iff
  rw [hkernel, Lp.eq_zero_iff_ae_eq_zero]
  change (∀ᵐ y ∂(cuspHorizontalMeasure w univ) • cuspVerticalMeasure Y,
    U.toContinuousLinearMap.adjoint f y = 0) ↔ _
  rw [Measure.ae_ennreal_smul_measure_iff
      (by simpa using ENNReal.ofReal_ne_zero_iff.mpr hw : cuspHorizontalMeasure w univ ≠ 0)]
  apply Filter.eventually_congr
  filter_upwards [cuspVerticalAdjoint_ae_horizontalMean w Y hw f] with y hy
  change (U.toContinuousLinearMap.adjoint f y = 0) ↔ cuspHorizontalMean w f y = 0
  rw [hy]

/-- The closed kernel is precisely horizontal mean zero for almost every
height, with respect to the actual density `dy / y²`. -/
theorem mem_cuspMeanZeroL2_iff (w Y : ℝ) (hw : 0 < w)
    (f : CuspStripL2 w Y) :
    f ∈ cuspMeanZeroL2 w Y ↔
      ∀ᵐ y ∂cuspVerticalMeasure Y, (∫ t in Ioc 0 w, f (t, y)) = 0 := by
  change cuspAverageProjection w Y f = 0 ↔ _
  rw [cuspAverageProjection_eq_zero_iff w Y hw f]
  apply Filter.eventually_congr
  filter_upwards with y
  simp only [cuspHorizontalMean, Pi.zero_apply, mul_eq_zero, inv_eq_zero,
    Complex.ofReal_eq_zero, hw.ne', false_or]

theorem cuspAverageProjection_orthogonal_residual (w Y : ℝ) (f : CuspStripL2 w Y) :
    inner ℂ (cuspAverageProjection w Y f) (f - cuspAverageProjection w Y f) = 0 := by
  rw [cuspAverageProjection_inner, map_sub, cuspAverageProjection_idempotent,
    sub_self, inner_zero_right]

theorem cuspAverageProjection_pythagoras (w Y : ℝ) (f : CuspStripL2 w Y) :
    ‖f‖ ^ 2 = ‖cuspAverageProjection w Y f‖ ^ 2 +
      ‖f - cuspAverageProjection w Y f‖ ^ 2 := by
  simpa only [add_sub_cancel, pow_two] using
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (cuspAverageProjection w Y f) (f - cuspAverageProjection w Y f)
      (cuspAverageProjection_orthogonal_residual w Y f)

theorem cuspMeanZeroL2_norm_sub_average_le (w Y : ℝ) (f : CuspStripL2 w Y) :
    ‖f - cuspAverageProjection w Y f‖ ≤ ‖f‖ := by
  have h := cuspAverageProjection_pythagoras w Y f
  nlinarith [sq_nonneg ‖cuspAverageProjection w Y f‖, norm_nonneg f,
    norm_nonneg (f - cuspAverageProjection w Y f)]

end ArtinMatthews
