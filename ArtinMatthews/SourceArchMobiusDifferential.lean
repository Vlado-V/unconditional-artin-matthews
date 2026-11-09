module

public import ArtinMatthews.SourceArchMobiusCoordinates
public import ArtinMatthews.SourceArchEuclideanSimilarities
public import ArtinMatthews.SourceArchGradientIsometry


set_option backward.privateInPublic true
@[expose] public section

/-! Every genuine Mobius differential is a positive similarity with its height ratio. -/
namespace ArtinMatthews.SourceArchJacquet
open Matrix OAI.CubicEisenstein Filter
open scoped MatrixGroups Topology
noncomputable section

def SourceArchMobiusMetricAt (g : SL(2, ℂ)) (p : EuclideanSpatial) : Prop :=
  ∃ (r : ℝ) (D : EuclideanSpatial →L[ℝ] EuclideanSpatial), 0 < r ∧
    HasFDerivAt (sourceArchMobiusEuclidean g) D p ∧
    (∀ v, ‖D v‖ = r * ‖v‖) ∧ sourceArchMobiusEuclidean g p 2 = r * p 2

lemma sourceArch_positive_eventually (p : EuclideanSpatial) (hp : 0 < p 2) :
    ∀ᶠ q in 𝓝 p, 0 < q 2 :=
  (isOpen_lt continuous_const (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (2 : Fin 3))).mem_nhds hp

lemma sourceArchMobiusMetricAt_translation (b : ℂ) (p : EuclideanSpatial) (hp : 0 < p 2) :
    SourceArchMobiusMetricAt (complexTranslation b) p := by
  refine ⟨1, ContinuousLinearMap.id ℝ EuclideanSpatial, zero_lt_one, ?_, ?_, ?_⟩
  · apply ((hasFDerivAt_id p).add_const (euclideanHorizontalTranslation b)).congr_of_eventuallyEq
    filter_upwards [sourceArch_positive_eventually p hp] with q hq
    exact sourceArchMobiusEuclidean_translation b q hq
  · intro v
    simp
  · rw [sourceArchMobiusEuclidean_translation b p hp]
    simp [euclideanHorizontalTranslation]

lemma sourceArchMobiusMetricAt_diagonal (b : ℂ) (hb : b ≠ 0)
    (p : EuclideanSpatial) (hp : 0 < p 2) :
    SourceArchMobiusMetricAt (complexDiagonal b hb) p := by
  refine ⟨Complex.normSq b, euclideanComplexDilation b, Complex.normSq_pos.mpr hb, ?_,
    sourceArchComplexDilation_norm b, ?_⟩
  · apply (euclideanComplexDilation b).hasFDerivAt.congr_of_eventuallyEq
    filter_upwards [sourceArch_positive_eventually p hp] with q hq
    exact sourceArchMobiusEuclidean_diagonal b hb q hq
  · rw [sourceArchMobiusEuclidean_diagonal b hb p hp]
    exact (euclideanComplexDilation_apply b p).2.2

lemma sourceArchMobiusMetricAt_weyl (p : EuclideanSpatial) (hp : 0 < p 2) :
    SourceArchMobiusMetricAt complexWeyl p := by
  have hn : p ≠ 0 := euclideanUpperHalf_ne_zero p hp
  refine ⟨(1 / ‖p‖) ^ 2, sourceArchWeylDerivative p,
    sq_pos_of_pos (one_div_pos.mpr (norm_pos_iff.mpr hn)), ?_, sourceArchWeylDerivative_norm p, ?_⟩
  · apply (sourceArchWeyl_hasFDerivAt p hn).congr_of_eventuallyEq
    filter_upwards [sourceArch_positive_eventually p hp] with q hq
    exact sourceArchMobiusEuclidean_weyl q hq
  · rw [sourceArchMobiusEuclidean_weyl p hp]
    exact (euclideanWeylAction_apply p).2.2

lemma sourceArchMobiusMetricAt_mul (g h : SL(2, ℂ))
    (hg : ∀ p, 0 < p 2 → SourceArchMobiusMetricAt g p)
    (hh : ∀ p, 0 < p 2 → SourceArchMobiusMetricAt h p)
    (p : EuclideanSpatial) (hp : 0 < p 2) :
    SourceArchMobiusMetricAt (g * h) p := by
  obtain ⟨rh, Dh, hrh, hDh, hNh, hYh⟩ := hh p hp
  obtain ⟨rg, Dg, hrg, hDg, hNg, hYg⟩ :=
    hg (sourceArchMobiusEuclidean h p) (sourceArchMobiusEuclidean_positive h p hp)
  refine ⟨rg * rh, Dg.comp Dh, mul_pos hrg hrh, ?_, ?_, ?_⟩
  · apply (hDg.comp p hDh).congr_of_eventuallyEq
    filter_upwards [sourceArch_positive_eventually p hp] with q hq
    exact sourceArchMobiusEuclidean_mul g h q hq
  · intro v
    rw [ContinuousLinearMap.comp_apply, hNg, hNh]
    ring
  · rw [sourceArchMobiusEuclidean_mul g h p hp, hYg, hYh]
    ring

theorem sourceArchMobiusEuclidean_metric (g : SL(2, ℂ)) :
    ∀ p, 0 < p 2 → SourceArchMobiusMetricAt g p := by
  by_cases hc : g 1 0 = 0
  · obtain ⟨ha, hg⟩ := complex_bruhat_zero g hc
    rw [hg]
    exact sourceArchMobiusMetricAt_mul _ _ (sourceArchMobiusMetricAt_diagonal _ ha)
      (sourceArchMobiusMetricAt_translation _)
  · rw [complex_bruhat_nonzero g hc]
    exact sourceArchMobiusMetricAt_mul _ _
      (sourceArchMobiusMetricAt_mul _ _
        (sourceArchMobiusMetricAt_mul _ _ (sourceArchMobiusMetricAt_translation _)
          (sourceArchMobiusMetricAt_diagonal _ (inv_ne_zero hc)))
        sourceArchMobiusMetricAt_weyl)
      (sourceArchMobiusMetricAt_translation _)

theorem sourceArchMobiusEuclidean_isometric_differential (g : SL(2, ℂ))
    (p : EuclideanSpatial) (hp : 0 < p 2) :
    ∃ (r : ℝ) (e : EuclideanSpatial ≃ₗᵢ[ℝ] EuclideanSpatial), 0 < r ∧
      HasFDerivAt (sourceArchMobiusEuclidean g)
        (r • e.toContinuousLinearEquiv.toContinuousLinearMap) p ∧
      sourceArchMobiusEuclidean g p 2 = r * p 2 := by
  obtain ⟨r, D, hr, hD, hN, hY⟩ := sourceArchMobiusEuclidean_metric g p hp
  obtain ⟨e, he⟩ := sourceArch_scaled_linearIsometry D r hr hN
  refine ⟨r, e, hr, ?_, hY⟩
  rwa [← he]

end
end ArtinMatthews.SourceArchJacquet
