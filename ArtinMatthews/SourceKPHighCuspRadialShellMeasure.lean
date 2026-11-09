module

public import ArtinMatthews.SourceKPHighCuspRadialMeasure


set_option backward.privateInPublic true
@[expose] public section

/-! Exact radial transport of left-open, right-closed high-cusp shells. -/
namespace ArtinMatthews
open NumberField Matrix Topology MeasureTheory Set
open scoped NumberField MatrixGroups AdeleRing ENNReal
noncomputable section
variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPHighCuspRadialHomeomorph_restrict_measure (t T : ℝ) (hT : 1 < T)
    (htT : 1 < sourceKPRadialHeightScale K t*T)
    (A : Set (SourceKPHighCuspAutomorphic K hζ (sourceKPRadialHeightScale K t*T))) :
    Measure.map (sourceKPHighCuspRadialHomeomorph K hζ t T hT htT)
      ((sourceKPHighCuspMeasure K hζ T).restrict
        ((sourceKPHighCuspRadialHomeomorph K hζ t T hT htT) ⁻¹' A)) =
      ENNReal.ofReal (sourceKPRadialHeightScale K t) •
        (sourceKPHighCuspMeasure K hζ (sourceKPRadialHeightScale K t*T)).restrict A := by
  rw [← (sourceKPHighCuspRadialHomeomorph K hζ t T hT htT).measurableEmbedding.restrict_map,
    sourceKPHighCuspRadialHomeomorph_map_measure, Measure.restrict_smul]

theorem sourceKPHighCuspRadialHomeomorph_shell_map (t T U : ℝ) (hT : 1 < T)
    (htT : 1 < sourceKPRadialHeightScale K t*T) :
    Measure.map (sourceKPHighCuspRadialHomeomorph K hζ t T hT htT)
      ((sourceKPHighCuspMeasure K hζ T).restrict
        {q | sourceKPAutomorphicOrbitHeight K hζ q.val ≤ U}) =
      ENNReal.ofReal (sourceKPRadialHeightScale K t) •
        (sourceKPHighCuspMeasure K hζ (sourceKPRadialHeightScale K t*T)).restrict
          {q | sourceKPAutomorphicOrbitHeight K hζ q.val ≤ sourceKPRadialHeightScale K t*U} := by
  have hp : (sourceKPHighCuspRadialHomeomorph K hζ t T hT htT) ⁻¹'
      {q | sourceKPAutomorphicOrbitHeight K hζ q.val ≤ sourceKPRadialHeightScale K t*U} =
      {q | sourceKPAutomorphicOrbitHeight K hζ q.val ≤ U} := by
    ext q
    change sourceKPAutomorphicOrbitHeight K hζ
      (sourceKPHighCuspRadialHomeomorph K hζ t T hT htT q).val ≤
        sourceKPRadialHeightScale K t*U ↔ _
    rw [sourceKPHighCuspRadialHomeomorph_height]
    exact mul_le_mul_iff_right₀ (sourceKPRadialHeightScale_pos K t)
  rw [← hp]
  exact sourceKPHighCuspRadialHomeomorph_restrict_measure K hζ t T hT htT _

theorem sourceKPHighCuspMeasure_map_val_restrict (T U : ℝ) :
    Measure.map Subtype.val ((sourceKPHighCuspMeasure K hζ T).restrict
      {q | sourceKPAutomorphicOrbitHeight K hζ q.val ≤ U}) =
      (sourceKPAutomorphicMeasure K hζ (sourceKPArchHaar K hζ)).restrict
        {q | T < sourceKPAutomorphicOrbitHeight K hζ q ∧ sourceKPAutomorphicOrbitHeight K hζ q ≤ U} := by
  let A : Set (SourceKPAutomorphicLevel K hζ) := {q | sourceKPAutomorphicOrbitHeight K hζ q ≤ U}
  have hA : MeasurableSet A :=
    (sourceKPAutomorphicOrbitHeight_sublevel_closed K hζ U).measurableSet
  have hval : MeasurableEmbedding
      (Subtype.val : SourceKPHighCuspAutomorphic K hζ T → SourceKPAutomorphicLevel K hζ) :=
    MeasurableEmbedding.subtype_coe (sourceKPHighCuspAutomorphic_isOpen K hζ T).measurableSet
  change Measure.map Subtype.val ((sourceKPHighCuspMeasure K hζ T).restrict (Subtype.val ⁻¹' A)) = _
  rw [← hval.restrict_map _ A, sourceKPHighCuspMeasure_map_val, Measure.restrict_restrict hA]
  congr 1
  ext q
  exact and_comm

theorem sourceKPHighCuspRadialValue_shell_map (t T U : ℝ) (hT : 1 < T)
    (htT : 1 < sourceKPRadialHeightScale K t*T) :
    Measure.map (sourceKPHighCuspRadialValue K hζ t T hT)
      ((sourceKPHighCuspMeasure K hζ T).restrict
        {q | sourceKPAutomorphicOrbitHeight K hζ q.val ≤ U}) =
      ENNReal.ofReal (sourceKPRadialHeightScale K t) •
        (sourceKPAutomorphicMeasure K hζ (sourceKPArchHaar K hζ)).restrict
          {q | sourceKPRadialHeightScale K t*T < sourceKPAutomorphicOrbitHeight K hζ q ∧
            sourceKPAutomorphicOrbitHeight K hζ q ≤ sourceKPRadialHeightScale K t*U} := by
  have he : sourceKPHighCuspRadialValue K hζ t T hT =
      Subtype.val ∘ sourceKPHighCuspRadialHomeomorph K hζ t T hT htT := by
    funext q
    exact (sourceKPHighCuspRadialHomeomorph_value K hζ t T hT htT q).symm
  rw [he, ← Measure.map_map measurable_subtype_coe
    (sourceKPHighCuspRadialHomeomorph K hζ t T hT htT).measurable,
    sourceKPHighCuspRadialHomeomorph_shell_map,
    Measure.map_smul _ measurable_subtype_coe.aemeasurable,
    sourceKPHighCuspMeasure_map_val_restrict]

end
end ArtinMatthews
