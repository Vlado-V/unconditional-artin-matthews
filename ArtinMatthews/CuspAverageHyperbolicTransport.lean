module

public import ArtinMatthews.CuspAverageProjection
public import ArtinMatthews.SpectralHyperbolicFiniteVolume
public import ArtinMatthews.SpectralCuspMass


set_option backward.privateInPublic true
@[expose] public section

/-! Exact product-strip/invariant-hyperbolic-measure transport for the actual averaging operator. -/
noncomputable section
namespace ArtinMatthews

open MeasureTheory Set
open scoped NNReal ENNReal

theorem cusp_upperHalfPlane_density (z : UpperHalfPlane) :
    (↑((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0)^2) : ℝ≥0∞) =
      ENNReal.ofReal (z.im^(-2 : ℤ)) := by
  have he : z.im^(-2 : ℤ) = (((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0)^2) : ℝ) := by
    simp only [zpow_neg, zpow_ofNat, NNReal.coe_div, NNReal.coe_one,
      NNReal.coe_mk]
    field_simp
  rw [he]
  rw [ENNReal.ofReal_pow (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal, ENNReal.coe_pow]

theorem cusp_upperHalfPlane_lintegral_coordinates (G : ℝ × ℝ → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ z : UpperHalfPlane, G (z.re,z.im)) =
      ∫⁻ p in {p : ℝ × ℝ | 0 < p.2}, ENNReal.ofReal (p.2^(-2 : ℤ))*G p := by
  have hcoe : MeasurePreserving UpperHalfPlane.coe
      (volume.comap UpperHalfPlane.coe) (volume.restrict (range UpperHalfPlane.coe)) :=
    ⟨UpperHalfPlane.measurable_coe, UpperHalfPlane.measurableEmbedding_coe.map_comap volume⟩
  let S : Set (ℝ × ℝ) := {p | 0 < p.2}
  have hprod : MeasurePreserving Complex.measurableEquivRealProd
      (volume.restrict (Complex.measurableEquivRealProd ⁻¹' S)) (volume.restrict S) := by
    refine ⟨Complex.measurableEquivRealProd.measurable, ?_⟩
    rw [← Complex.measurableEquivRealProd.restrict_map,
      Complex.volume_preserving_equiv_real_prod.map_eq]
  rw [UpperHalfPlane.volume_def,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  calc
    _ = ∫⁻ z : UpperHalfPlane, ENNReal.ofReal (z.im^(-2 : ℤ))*G (z.re,z.im)
        ∂volume.comap UpperHalfPlane.coe := by
      apply lintegral_congr
      intro z
      rw [Pi.mul_apply, cusp_upperHalfPlane_density]
    _ = ∫⁻ z : ℂ in range UpperHalfPlane.coe,
        ENNReal.ofReal (z.im^(-2 : ℤ))*G (z.re,z.im) :=
      hcoe.lintegral_comp_emb UpperHalfPlane.measurableEmbedding_coe
        (fun z : ℂ => ENNReal.ofReal (z.im^(-2 : ℤ))*G (z.re,z.im))
    _ = _ := by
      convert hprod.lintegral_comp_emb Complex.measurableEquivRealProd.measurableEmbedding
        (fun p => ENNReal.ofReal (p.2^(-2 : ℤ))*G p) using 1
      rw [UpperHalfPlane.range_coe]
      rfl

theorem cusp_upperHalfPlane_setLIntegral_coordinates (G : ℝ × ℝ → ℝ≥0∞) (hG : Measurable G)
    {S : Set (ℝ × ℝ)} (hS : MeasurableSet S)
    (hpositive : S ⊆ {p : ℝ × ℝ | 0 < p.2}) :
    (∫⁻ z : UpperHalfPlane in {z | (z.re,z.im) ∈ S}, G (z.re,z.im)) =
      ∫⁻ p in S, ENNReal.ofReal (p.2^(-2 : ℤ))*G p := by
  classical
  have hh := cusp_upperHalfPlane_lintegral_coordinates (S.indicator G) (hG.indicator hS)
  have hl : (fun z : UpperHalfPlane => S.indicator G (z.re,z.im)) =
      {z : UpperHalfPlane | (z.re,z.im) ∈ S}.indicator (fun z => G (z.re,z.im)) := rfl
  have hr : (fun p : ℝ × ℝ => ENNReal.ofReal (p.2^(-2 : ℤ))*S.indicator G p) =
      S.indicator (fun p => ENNReal.ofReal (p.2^(-2 : ℤ))*G p) := by
    funext p
    by_cases hp : p ∈ S <;> simp [hp]
  have hpre : MeasurableSet {z : UpperHalfPlane | (z.re,z.im) ∈ S} := hS.preimage (by fun_prop)
  rw [hl, lintegral_indicator hpre, hr, lintegral_indicator hS,
    Measure.restrict_restrict_of_subset hpositive] at hh
  exact hh

theorem cuspStripMeasure_eq_density (w Y : ℝ) :
    cuspStripMeasure w Y =
      (volume.restrict ((Ioc 0 w) ×ˢ (Ioi Y))).withDensity
        (fun p : ℝ × ℝ => ENNReal.ofReal (p.2^(-2 : ℤ))) := by
  unfold cuspStripMeasure cuspHorizontalMeasure cuspVerticalMeasure
  rw [prod_withDensity_right (by fun_prop), Measure.prod_restrict]
  rfl

/-- Coordinates preserve the actual unnormalized product-strip measure,
including the full cusp width and the invariant vertical density. -/
theorem cusp_coordinates_measurePreserving (w Y : ℝ) (hY : 0 < Y) :
    MeasurePreserving (fun z : UpperHalfPlane => (z.re,z.im))
      (volume.restrict (hyperbolicCuspStrip w Y)) (cuspStripMeasure w Y) := by
  have hm : Measurable (fun z : UpperHalfPlane => (z.re,z.im)) := by fun_prop
  refine ⟨hm, Measure.ext_of_lintegral _ fun G hG => ?_⟩
  rw [lintegral_map hG hm, cuspStripMeasure_eq_density,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hG]
  exact cusp_upperHalfPlane_setLIntegral_coordinates G hG
    (measurableSet_Ioc.prod measurableSet_Ioi) (fun p hp => hY.trans hp.2)

def cuspHyperbolicPullback (w Y : ℝ) (hY : 0 < Y) :
    CuspStripL2 w Y →ₗᵢ[ℂ] Lp ℂ 2 (volume.restrict (hyperbolicCuspStrip w Y)) :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun z : UpperHalfPlane => (z.re,z.im))
    (cusp_coordinates_measurePreserving w Y hY)

theorem cuspHyperbolicPullback_ae (w Y : ℝ) (hY : 0 < Y) (f : CuspStripL2 w Y) :
    cuspHyperbolicPullback w Y hY f =ᵐ[volume.restrict (hyperbolicCuspStrip w Y)]
      (fun z : UpperHalfPlane => f (z.re,z.im)) :=
  Lp.coeFn_compMeasurePreserving _ _

theorem cuspHyperbolicPullback_residual_ae (w Y : ℝ) (hw : 0 < w) (hY : 0 < Y)
    (f : CuspStripL2 w Y) :
    cuspHyperbolicPullback w Y hY (f-cuspAverageProjection w Y f)
      =ᵐ[volume.restrict (hyperbolicCuspStrip w Y)]
        (fun z : UpperHalfPlane => cuspMeanZeroRepresentative w f (z.re,z.im)) :=
  (cuspHyperbolicPullback_ae w Y hY _).trans
    ((cusp_coordinates_measurePreserving w Y hY).quasiMeasurePreserving.ae_eq_comp
      (cuspMeanZeroL2_ae_representative w Y hw f))

end ArtinMatthews
