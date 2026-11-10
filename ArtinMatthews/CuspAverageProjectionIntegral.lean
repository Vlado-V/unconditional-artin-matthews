module

public import ArtinMatthews.CuspAverageProjectionOperator
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Integral.Prod


set_option backward.privateInPublic true
@[expose] public section

/-! Identification of the actual Hilbert-space projection with horizontal integration. -/
noncomputable section
namespace ArtinMatthews
open MeasureTheory Set
open scoped ENNReal InnerProduct

private theorem strip_restrict_vertical (w Y : ℝ) (s : Set ℝ) :
    (cuspStripMeasure w Y).restrict (Prod.snd ⁻¹' s) =
      (cuspHorizontalMeasure w).prod ((cuspVerticalMeasure Y).restrict s) := by
  rw [show Prod.snd ⁻¹' s = (univ : Set ℝ) ×ˢ s by ext; simp]
  unfold cuspStripMeasure
  rw [← Measure.prod_restrict, Measure.restrict_univ]

private theorem strip_preimage_measure (w Y : ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    cuspStripMeasure w Y (Prod.snd ⁻¹' s) =
      ((cuspHorizontalMeasure w univ) • cuspVerticalMeasure Y) s := by
  exact (show MeasurePreserving Prod.snd (cuspStripMeasure w Y)
    ((cuspHorizontalMeasure w univ) • cuspVerticalMeasure Y) from
    ⟨measurable_snd, Measure.map_snd_prod⟩).measure_preimage hs.nullMeasurableSet

private theorem strip_integrable_vertical_restrict (w Y : ℝ) (f : CuspStripL2 w Y)
    {s : Set ℝ} (hs : MeasurableSet s)
    (hfin : ((cuspHorizontalMeasure w univ) • cuspVerticalMeasure Y) s ≠ ∞) :
    Integrable f ((cuspHorizontalMeasure w).prod ((cuspVerticalMeasure Y).restrict s)) := by
  rw [← strip_restrict_vertical]
  exact integrableOn_Lp_of_measure_ne_top f (by norm_num)
    (by rwa [strip_preimage_measure w Y hs])

theorem cuspHorizontalMean_integrableOn (w Y : ℝ) (f : CuspStripL2 w Y)
    {s : Set ℝ} (hs : MeasurableSet s)
    (hfin : ((cuspHorizontalMeasure w univ) • cuspVerticalMeasure Y) s ≠ ∞) :
    IntegrableOn (cuspHorizontalMean w f) s
      ((cuspHorizontalMeasure w univ) • cuspVerticalMeasure Y) := by
  have h := (strip_integrable_vertical_restrict w Y f hs hfin).integral_prod_right
  have h' := (h.const_mul (w : ℂ)⁻¹).smul_measure (c := cuspHorizontalMeasure w univ)
    (by simp)
  change Integrable (fun y => (w : ℂ)⁻¹ * ∫ t, f (t, y) ∂cuspHorizontalMeasure w)
    (((cuspHorizontalMeasure w univ) • cuspVerticalMeasure Y).restrict s)
  rw [Measure.restrict_smul]
  exact h'

theorem cuspVerticalAdjoint_setIntegral (w Y : ℝ) (f : CuspStripL2 w Y)
    {s : Set ℝ} (hs : MeasurableSet s)
    (hfin : ((cuspHorizontalMeasure w univ) • cuspVerticalMeasure Y) s ≠ ∞) :
    (∫ y in s, ((cuspVerticalPullback w Y).toContinuousLinearMap.adjoint f) y
      ∂((cuspHorizontalMeasure w univ) • cuspVerticalMeasure Y)) =
      ∫ y in s, ∫ x, f (x, y) ∂cuspHorizontalMeasure w ∂cuspVerticalMeasure Y := by
  rw [← L2.inner_indicatorConstLp_one hs hfin]
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ
    (Lp.compMeasurePreserving Prod.snd
      ⟨measurable_snd, Measure.map_snd_prod⟩ (indicatorConstLp 2 hs hfin (1 : ℂ))) f = _
  rw [Lp.indicatorConstLp_compMeasurePreserving]
  erw [L2.inner_indicatorConstLp_one]
  change (∫ z in Prod.snd ⁻¹' s, f z ∂cuspStripMeasure w Y) = _
  rw [strip_restrict_vertical]
  exact integral_prod_symm f (strip_integrable_vertical_restrict w Y f hs hfin)

theorem cuspHorizontalMean_setIntegral (w Y : ℝ) (hw : 0 < w)
    (f : CuspStripL2 w Y) (s : Set ℝ) :
    (∫ y in s, cuspHorizontalMean w f y
      ∂((cuspHorizontalMeasure w univ) • cuspVerticalMeasure Y)) =
      ∫ y in s, ∫ x, f (x, y) ∂cuspHorizontalMeasure w ∂cuspVerticalMeasure Y := by
  rw [Measure.restrict_smul, integral_smul_measure, cuspHorizontalMeasure_univ,
    ENNReal.toReal_ofReal hw.le]
  simp only [cuspHorizontalMean, integral_const_mul, cuspHorizontalMeasure,
    Complex.real_smul]
  rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hw.ne'), one_mul]

theorem cuspVerticalAdjoint_ae_horizontalMean (w Y : ℝ) (hw : 0 < w)
    (f : CuspStripL2 w Y) :
    ((cuspVerticalPullback w Y).toContinuousLinearMap.adjoint f : ℝ → ℂ)
      =ᵐ[cuspVerticalMeasure Y] cuspHorizontalMean w f := by
  have heq : ((cuspVerticalPullback w Y).toContinuousLinearMap.adjoint f : ℝ → ℂ)
      =ᵐ[(cuspHorizontalMeasure w univ) • cuspVerticalMeasure Y] cuspHorizontalMean w f := by
    have : SigmaFinite ((cuspHorizontalMeasure w univ) • cuspVerticalMeasure Y) := by
      rw [cuspHorizontalMeasure_univ, ENNReal.ofReal]
      change SigmaFinite (w.toNNReal • cuspVerticalMeasure Y)
      infer_instance
    apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    · intro s _ hs
      exact integrableOn_Lp_of_measure_ne_top _ (by norm_num) hs.ne
    · intro s hs hfin
      exact cuspHorizontalMean_integrableOn w Y f hs hfin.ne
    · intro s hs hfin
      rw [cuspVerticalAdjoint_setIntegral w Y f hs hfin.ne,
        cuspHorizontalMean_setIntegral w Y hw f s]
  exact (Measure.ae_ennreal_smul_measure_iff
    (by simpa using (ENNReal.ofReal_ne_zero_iff.mpr hw) : cuspHorizontalMeasure w univ ≠ 0)).mp heq

end ArtinMatthews
