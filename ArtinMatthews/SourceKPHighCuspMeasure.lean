module

public import ArtinMatthews.SourceKPAutomorphicChartMeasure
public import ArtinMatthews.SourceKPArchRadialHaar


set_option backward.privateInPublic true
@[expose] public section

/-! The actual automorphic measure restricted to the genuine high-cusp subtype. -/
namespace ArtinMatthews
open NumberField Matrix Topology MeasureTheory Set
open scoped NumberField MatrixGroups AdeleRing ENNReal
noncomputable section
variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPHighCuspAutomorphic_isOpen (T : ℝ) :
    IsOpen {x : SourceKPAutomorphicLevel K hζ | T < sourceKPAutomorphicOrbitHeight K hζ x} := by
  simpa only [Set.compl_ofPred, not_le] using
    (sourceKPAutomorphicOrbitHeight_sublevel_closed K hζ T).isOpen_compl

def sourceKPHighCuspMeasure (T : ℝ) : Measure (SourceKPHighCuspAutomorphic K hζ T) :=
  Measure.comap Subtype.val (sourceKPAutomorphicMeasure K hζ (sourceKPArchHaar K hζ))

theorem sourceKPHighCuspMeasure_apply (T : ℝ) (A : Set (SourceKPHighCuspAutomorphic K hζ T)) :
    sourceKPHighCuspMeasure K hζ T A =
      sourceKPAutomorphicMeasure K hζ (sourceKPArchHaar K hζ) (Subtype.val '' A) :=
  (MeasurableEmbedding.subtype_coe (sourceKPHighCuspAutomorphic_isOpen K hζ T).measurableSet).comap_apply _ A

theorem sourceKPHighCuspMeasure_map_val (T : ℝ) :
    Measure.map Subtype.val (sourceKPHighCuspMeasure K hζ T) =
      (sourceKPAutomorphicMeasure K hζ (sourceKPArchHaar K hζ)).restrict
        {x | T < sourceKPAutomorphicOrbitHeight K hζ x} :=
  map_comap_subtype_coe (sourceKPHighCuspAutomorphic_isOpen K hζ T).measurableSet
    (sourceKPAutomorphicMeasure K hζ (sourceKPArchHaar K hζ))

theorem sourceKPHighCusp_representative (T : ℝ) (q : SourceKPHighCuspAutomorphic K hζ T) :
    ∃ x : SourceKPHighCuspFinite K hζ T, sourceKPHighCuspProjection K hζ T x = q := by
  obtain ⟨x,hx⟩ := sourceKPHighCuspQuotientMap_surjective K hζ T q
  obtain ⟨x,rfl⟩ := Quotient.mk_surjective x
  exact ⟨x,hx⟩

end
end ArtinMatthews
