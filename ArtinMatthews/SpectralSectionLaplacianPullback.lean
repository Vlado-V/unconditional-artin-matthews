module

public import ArtinMatthews.SpectralModularDensitySeeds
public import ArtinMatthews.SpectralSectionComplexGreen
public import ArtinMatthews.SpectralSectionLaplacianSeed
public import ArtinMatthews.SpectralSectionGradientPairing
public import ArtinMatthews.SpectralGamma0CompactMass
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The actual positive hyperbolic Laplacian commutes with integral modular
pullback.  The proof uses the proved complex Green identity and gradient
covariance, with the genuine invariant measure and compact smooth tests. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff MatrixGroups InnerProductSpace

namespace ArtinMatthews

theorem h2_volume_isOpenPosMeasure :
    Measure.IsOpenPosMeasure (volume : Measure UpperHalfPlane) := by
  let : Measure.IsOpenPosMeasure (volume.comap UpperHalfPlane.coe) :=
    Measure.IsOpenPosMeasure.comap volume UpperHalfPlane.isOpenEmbedding_coe
  rw [UpperHalfPlane.volume_def]
  apply Measure.AbsolutelyContinuous.isOpenPosMeasure (μ := volume.comap UpperHalfPlane.coe)
  apply withDensity_absolutelyContinuous'
  · exact ((continuous_const.div₀ (show Continuous (fun z : UpperHalfPlane => (NNReal.mk z.im z.im_pos.le : NNReal)) from UpperHalfPlane.continuous_im.subtype_mk _)
      (fun z => NNReal.ne_iff.mp z.im_ne_zero)).pow 2).measurable.coe_nnreal_ennreal.aemeasurable
  · exact Filter.Eventually.of_forall (fun z => by
      simp only [ne_eq, ENNReal.coe_eq_zero, pow_eq_zero_iff (by decide : 2 ≠ 0),
        div_eq_zero_iff, one_ne_zero, false_or]
      exact NNReal.ne_iff.mp z.im_ne_zero)

theorem h2SectionLaplacian_pullback_pairing (r : SL(2, ℤ))
    (ψ θ : h2SmoothCompactSeeds) :
    (∫ z : UpperHalfPlane,
      inner ℂ (h2SectionPositiveLaplacian (modularTranslateSmoothSeed r ψ).val z) (θ.val z)) =
    ∫ z : UpperHalfPlane, inner ℂ (h2SectionPositiveLaplacian ψ.val (r • z)) (θ.val z) := by
  let τ := modularTranslateSmoothSeed r⁻¹ θ
  have heq : (fun v : UpperHalfPlane => τ.val (r • v)) = θ.val := by
    funext v
    change θ.val (r⁻¹ • (r • v)) = θ.val v
    rw [inv_smul_smul]
  have hcov (z : UpperHalfPlane) :
      inner ℂ (h2SectionGradient (modularTranslateSmoothSeed r ψ).val z)
        (h2SectionGradient θ.val z) =
      inner ℂ (h2SectionGradient ψ.val (r • z)) (h2SectionGradient τ.val (r • z)) := by
    have h := h2SectionGradient_inner_pullback ψ.val τ.val ψ.property τ.property
      (Matrix.SpecialLinearGroup.mapGL ℝ r) (by simp) z
    change inner ℂ (h2SectionGradient (modularTranslateSmoothSeed r ψ).val z)
      (h2SectionGradient (fun v => τ.val (r • v)) z) = _ at h
    rwa [heq] at h
  have hme : MeasurableEmbedding (fun z : UpperHalfPlane => r • z) := by
    change MeasurableEmbedding (fun z : UpperHalfPlane => Matrix.SpecialLinearGroup.mapGL ℝ r • z)
    exact measurableEmbedding_const_smul _
  calc
    _ = ∫ z : UpperHalfPlane, inner ℂ
        (h2SectionGradient (modularTranslateSmoothSeed r ψ).val z)
        (h2SectionGradient θ.val z) := h2Section_compact_complex_green _ θ.val θ.property
    _ = ∫ z : UpperHalfPlane, inner ℂ (h2SectionGradient ψ.val (r • z))
        (h2SectionGradient τ.val (r • z)) := integral_congr_ae (Filter.Eventually.of_forall hcov)
    _ = ∫ z : UpperHalfPlane, inner ℂ (h2SectionGradient ψ.val z)
        (h2SectionGradient τ.val z) := (h2_integer_measurePreserving r).integral_comp hme (fun z : UpperHalfPlane => inner ℂ (h2SectionGradient ψ.val z) (h2SectionGradient τ.val z))
    _ = ∫ z : UpperHalfPlane, inner ℂ (h2SectionPositiveLaplacian ψ.val z) (τ.val z) :=
      (h2Section_compact_complex_green ψ τ.val τ.property).symm
    _ = ∫ z : UpperHalfPlane, inner ℂ (h2SectionPositiveLaplacian ψ.val (r • z))
        (τ.val (r • z)) := ((h2_integer_measurePreserving r).integral_comp hme _).symm
    _ = _ := by simp only [τ, modularTranslateSmoothSeed_apply, inv_smul_smul]

theorem h2SectionPositiveLaplacian_modular_pullback (r : SL(2, ℤ))
    (ψ : h2SmoothCompactSeeds) (z : UpperHalfPlane) :
    h2SectionPositiveLaplacian (fun w => ψ.val (r • w)) z =
      h2SectionPositiveLaplacian ψ.val (r • z) := by
  let u := h2SectionLaplacianSeed (modularTranslateSmoothSeed r ψ)
  let v := modularTranslateSmoothSeed r (h2SectionLaplacianSeed ψ)
  let δ : h2SmoothCompactSeeds := u-v
  have hu : MemLp u.val 2 (volume : Measure UpperHalfPlane) :=
    u.val.continuous.memLp_of_hasCompactSupport u.val.hasCompactSupport
  have hv : MemLp v.val 2 (volume : Measure UpperHalfPlane) :=
    v.val.continuous.memLp_of_hasCompactSupport v.val.hasCompactSupport
  have hd : MemLp δ.val 2 (volume : Measure UpperHalfPlane) :=
    δ.val.continuous.memLp_of_hasCompactSupport δ.val.hasCompactSupport
  have he : inner ℂ (hu.toLp u.val-hv.toLp v.val) (hd.toLp δ.val) = 0 := by
    rw [inner_sub_left, L2.inner_def, L2.inner_def]
    have huδ : (∫ x, inner ℂ ((hu.toLp u.val) x) ((hd.toLp δ.val) x)) =
        ∫ x, inner ℂ (u.val x) (δ.val x) := by
      apply integral_congr_ae
      filter_upwards [hu.coeFn_toLp,hd.coeFn_toLp] with x hx hy
      rw [hx,hy]
    have hvδ : (∫ x, inner ℂ ((hv.toLp v.val) x) ((hd.toLp δ.val) x)) =
        ∫ x, inner ℂ (v.val x) (δ.val x) := by
      apply integral_congr_ae
      filter_upwards [hv.coeFn_toLp,hd.coeFn_toLp] with x hx hy
      rw [hx,hy]
    rw [huδ,hvδ]
    exact sub_eq_zero.mpr (h2SectionLaplacian_pullback_pairing r ψ δ)
  have hLp : hu.toLp u.val-hv.toLp v.val = hd.toLp δ.val := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub (hu.toLp u.val) (hv.toLp v.val),
      hu.coeFn_toLp,hv.coeFn_toLp,hd.coeFn_toLp] with x hsub hx hy hz
    simp only [hsub,Pi.sub_apply,hx,hy,hz]
    rfl
  rw [hLp] at he
  have hzero := inner_self_eq_zero.mp he
  have hae : δ.val =ᵐ[(volume : Measure UpperHalfPlane)] 0 := by
    apply hd.coeFn_toLp.symm.trans
    rw [hzero]
    exact Lp.coeFn_zero ℂ 2 volume
  let := h2_volume_isOpenPosMeasure
  have hpoint := Measure.eq_of_ae_eq hae δ.val.continuous continuous_const
  have hz := congrFun hpoint z
  exact sub_eq_zero.mp hz

theorem h2SectionLaplacianSeed_modular_pullback (r : SL(2, ℤ))
    (ψ : h2SmoothCompactSeeds) :
    h2SectionLaplacianSeed (modularTranslateSmoothSeed r ψ) =
      modularTranslateSmoothSeed r (h2SectionLaplacianSeed ψ) := by
  apply Subtype.ext
  ext z
  exact h2SectionPositiveLaplacian_modular_pullback r ψ z

end ArtinMatthews
