module

public import ArtinMatthews.SourceEisensteinHighOutgoingBound
public import ArtinMatthews.SourceKPHighCuspMeasure
public import ArtinMatthews.SourceKPAutomorphicMeasureRegularity
public import ArtinMatthews.SourceKPCompactHeight


set_option backward.privateInPublic true
@[expose] public section

/-! The literal closed high bands are compact in the framed and compact
automorphic quotients. This also controls the supports of high-cusp tests. -/
namespace ArtinMatthews
open NumberField Matrix Topology Set MeasureTheory
open scoped NumberField MatrixGroups AdeleRing ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "X" => SourceKPAutomorphicLevel K hζ
local notation "H" => sourceKPAutomorphicOrbitHeight K hζ

theorem sourceKPAutomorphicCompactOrbitHeight_pos (y : SourceKPAutomorphicCompactLevel K hζ) :
    0 < sourceKPAutomorphicCompactOrbitHeight K hζ y := by
  obtain ⟨c,hc,hheight⟩ := sourceKPAutomorphicCompactOrbitHeight_uniform_pos K hζ
  exact hc.trans_le (hheight y)

theorem sourceKPHighCuspProjection_orbitHeight (T : ℝ) (hT : 1 < T)
    (x : SourceKPHighCuspFinite K hζ T) :
    H (sourceKPHighCuspProjection K hζ T x).val =
      sourceKPFiniteLevelHeight K hζ x.val := by
  change H (Quotient.mk _ x.val) = _
  rw [sourceKPAutomorphicOrbitHeight_of_finite,
    sourceKPFiniteLevelOrbitHeight_eq_height_of_high K hζ x.val (hT.trans x.property)]

theorem sourceKPHighCuspHeight_continuous (T : ℝ) (hT : 1 < T) :
    Continuous (fun x : SourceKPHighCuspAutomorphic K hζ T => H x.val) := by
  let f : SourceKPHighCuspAutomorphic K hζ T → ℝ := fun x => H x.val
  let e := sourceKPHighCuspHomeomorph K hζ T hT
  have hc : Continuous (f ∘ e) := by
    apply isQuotientMap_quotient_mk'.continuous_iff.mpr
    change Continuous (fun x : SourceKPHighCuspFinite K hζ T => f (e (Quotient.mk _ x)))
    have he : (fun x : SourceKPHighCuspFinite K hζ T => f (e (Quotient.mk _ x))) =
        sourceKPFiniteLevelHeight K hζ ∘ Subtype.val := by
      funext x
      change H (e (Quotient.mk _ x)).val = sourceKPFiniteLevelHeight K hζ x.val
      dsimp only [e]
      rw [sourceKPHighCuspHomeomorph_mk]
      exact sourceKPHighCuspProjection_orbitHeight K hζ T hT x
    rw [he]
    exact (sourceKPFiniteLevelHeight_continuous K hζ).comp continuous_subtype_val
  simpa only [Function.comp_def,Homeomorph.apply_symm_apply] using hc.comp e.symm.continuous

theorem sourceKPAutomorphicHighBand_isCompact (L U : ℝ) (hL : 1 < L) (hLU : L ≤ U) :
    IsCompact {x : X | H x ∈ Icc L U} := by
  let v₀ : InfinitePlace K := Classical.choice inferInstance
  let S := sourceKPHeightBandMatrices K hζ v₀ (Real.log L) (Real.log U)
  let A := sourceKPCompactLevelContainer K hζ S ∩
    (sourceKPFiniteLevelHeight K hζ) ⁻¹' Icc L U
  let π : SourceKPFiniteLevelSpace K hζ → X := Quotient.mk _
  have hS := sourceKPHeightBandMatrices_isCompact K hζ v₀ (Real.log L) (Real.log U)
  have hA : IsCompact A := (sourceKPCompactLevelContainer_isCompact K hζ S hS).inter_right
    (isClosed_Icc.preimage (sourceKPFiniteLevelHeight_continuous K hζ))
  have hπ : Continuous π := continuous_quot_mk
  suffices {x : X | H x ∈ Icc L U} = π '' A by rw [this]; exact hA.image hπ
  ext x
  constructor
  · intro hx
    let T : ℝ := (1+L)/2
    have hT : 1 < T := by dsimp only [T]; linarith
    have hTL : T < L := by dsimp only [T]; linarith
    let z : SourceKPHighCuspAutomorphic K hζ T := ⟨x,hTL.trans_le hx.1⟩
    obtain ⟨w,hw⟩ := sourceKPHighCusp_representative K hζ T z
    obtain ⟨q,hq⟩ := sourceKPFiniteLevelMk_surjective K hζ w.val
    have hqx : sourceKPAutomorphicLevelMk K hζ q = x := by
      change π (sourceKPFiniteLevelMk K hζ q) = _
      rw [hq]
      exact congrArg Subtype.val hw
    have hH : sourceKPAdelicCoverHeight K hζ q = H x := by
      rw [← sourceKPFiniteLevelHeight_mk, hq,
        ← sourceKPHighCuspProjection_orbitHeight K hζ T hT w,hw]
    obtain ⟨g,hg⟩ := ProjGenLinGroup.mk_surjective (sourceKPAdelicProjectiveProjection K hζ q)
    have hHg : sourceKPAdelicHeight K hζ g = H x := by
      rw [← hH,sourceKPAdelicCoverHeight,← hg,sourceKPAdelicHeightOnProjective_mk]
    have hlog : Real.log (sourceKPAdelicHeight K hζ g) ∈ Icc (Real.log L) (Real.log U) := by
      exact ⟨Real.log_le_log (zero_lt_one.trans hL) (hHg.symm ▸ hx.1),
        Real.log_le_log (sourceKPAdelicHeight_pos K hζ g) (hHg.symm ▸ hx.2)⟩
    obtain ⟨γ,g',hg',he⟩ := sourceKPHeightBand_matrix_reduction K hζ v₀ _ _ g hlog
    let q' := sourceKPAdelicProjectiveRationalLift K hζ γ*q
    have hq' : sourceKPAdelicProjectiveProjection K hζ q' = ProjGenLinGroup.mk g' := by
      dsimp only [q']
      rw [map_mul,sourceKPAdelicProjectiveRationalLift_projection,← hg]
      exact he
    refine ⟨sourceKPFiniteLevelMk K hζ q',⟨sourceKPCompactLevelContainer_mem K hζ S q' g' hg' hq',?_⟩,?_⟩
    · change sourceKPFiniteLevelHeight K hζ (sourceKPFiniteLevelMk K hζ q') ∈ Icc L U
      rw [sourceKPFiniteLevelHeight_mk,sourceKPAdelicCoverHeight,hq',sourceKPAdelicHeightOnProjective_mk]
      have hb := sourceKPHeightBandMatrices_height K hζ v₀ _ _ g' hg'
      exact ⟨(Real.log_le_log_iff (zero_lt_one.trans hL) (sourceKPAdelicHeight_pos K hζ g')).mp hb.1,
        (Real.log_le_log_iff (sourceKPAdelicHeight_pos K hζ g') ((zero_lt_one.trans hL).trans_le hLU)).mp hb.2⟩
    · exact (sourceKPAutomorphicLevelMk_rational K hζ γ q).trans hqx
  · rintro ⟨y,hy,rfl⟩
    have hb : sourceKPFiniteLevelHeight K hζ y ∈ Icc L U := hy.2
    change sourceKPAutomorphicOrbitHeight K hζ (Quotient.mk _ y) ∈ Icc L U
    rw [sourceKPAutomorphicOrbitHeight_of_finite,
      sourceKPFiniteLevelOrbitHeight_eq_height_of_high K hζ y (hL.trans_le hb.1)]
    exact hb

theorem sourceKPHighCuspBand_isCompact (T L U : ℝ) (hT : 1 < T) (hTL : T < L) (hLU : L ≤ U) :
    IsCompact {x : SourceKPHighCuspAutomorphic K hζ T | H x.val ∈ Icc L U} := by
  rw [IsEmbedding.subtypeVal.isCompact_iff]
  have he : Subtype.val '' {x : SourceKPHighCuspAutomorphic K hζ T | H x.val ∈ Icc L U} =
      {x : X | H x ∈ Icc L U} := by
    ext x
    constructor
    · rintro ⟨q,hq,rfl⟩
      exact hq
    · intro hx
      exact ⟨⟨x,hTL.trans_le hx.1⟩,hx,rfl⟩
  rw [he]
  exact sourceKPAutomorphicHighBand_isCompact K hζ L U (hT.trans hTL) hLU

theorem sourceKPAutomorphicCompactHighBand_isCompact (L U : ℝ) (hL : 1 < L) (hLU : L ≤ U) :
    IsCompact {x : SourceKPAutomorphicCompactLevel K hζ |
      sourceKPAutomorphicCompactOrbitHeight K hζ x ∈ Icc L U} := by
  have he : {x : SourceKPAutomorphicCompactLevel K hζ |
      sourceKPAutomorphicCompactOrbitHeight K hζ x ∈ Icc L U} =
      sourceKPAutomorphicCompactMk K hζ '' {x : X | H x ∈ Icc L U} := by
    ext x
    induction x using Quotient.inductionOn with
    | _ y =>
      constructor
      · intro hy
        exact ⟨y,hy,rfl⟩
      · rintro ⟨z,hz,he⟩
        change sourceKPAutomorphicCompactOrbitHeight K hζ (Quotient.mk _ y) ∈ Icc L U
        rw [← he]
        exact hz
  rw [he]
  exact (sourceKPAutomorphicHighBand_isCompact K hζ L U hL hLU).image
    (sourceKPAutomorphicCompactMk_isOpenQuotientMap K hζ).continuous

theorem sourceKPHighCuspMeasure_finiteOnCompacts (T : ℝ) :
    IsFiniteMeasureOnCompacts (sourceKPHighCuspMeasure K hζ T) := by
  constructor
  intro A hA
  rw [sourceKPHighCuspMeasure_apply]
  exact (hA.image continuous_subtype_val).measure_lt_top

end
end ArtinMatthews
