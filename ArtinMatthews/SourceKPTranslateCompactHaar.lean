module

public import ArtinMatthews.SourceKPTranslateRepresentativeHaar


set_option backward.privateInPublic true
@[expose] public section

/-! The actual common-level compact Haar measure and its exact pushforward degrees. -/
namespace ArtinMatthews
open NumberField Matrix MeasureTheory Set Topology
open scoped NumberField MatrixGroups AdeleRing ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Γ" => PGL(2, K)
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "D" => sourceKPFiniteLevelConjugate K hζ
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)

variable (T : Finset (SourceKPFiniteAdeleProjective K hζ))
include T

local notation "J" => sourceKPFiniteTranslateLevel K hζ T
local notation "XJ" => SourceKPTranslateRepresentativeSpace K hζ T
local notation "YJ" => SourceKPTranslateAutomorphicCompactLevel K hζ T
local notation "νJ" => sourceKPTranslateRepresentativeHaar K hζ T
local notation "qJ" => sourceKPTranslateRepresentativeToCompact K hζ T

def sourceKPTranslateRepresentativeDomain (t : Gf) (h : J ≤ D t) : Set XJ :=
  sourceKPTranslateRepresentativeMap K hζ T t h ⁻¹' sourceKPTranslateBaseDomain K hζ

theorem sourceKPTranslateRepresentativeDomain_measurable (t : Gf) (h : J ≤ D t) :
    MeasurableSet (sourceKPTranslateRepresentativeDomain K hζ T t h) :=
  (sourceKPTranslateBaseDomain_measurable K hζ).preimage
    (sourceKPTranslateRepresentativeMap_measurable K hζ T t h)

theorem sourceKPTranslateRepresentativeDomain_isFundamental (t : Gf) (h : J ≤ D t) :
    IsFundamentalDomain Γ (sourceKPTranslateRepresentativeDomain K hζ T t h) νJ := by
  apply IsFundamentalDomain.mk'
    (sourceKPTranslateRepresentativeDomain_measurable K hζ T t h).nullMeasurableSet
  intro x
  simpa only [sourceKPTranslateRepresentativeDomain, Set.mem_preimage,
    sourceKPTranslateRepresentativeMap_rational] using
      sourceKPTranslateBaseDomain_existsUnique K hζ (sourceKPTranslateRepresentativeMap K hζ T t h x)

def sourceKPTranslateCompactHaar : Measure YJ :=
  Measure.map qJ ((νJ).restrict (sourceKPTranslateRepresentativeDomain K hζ T 1
    (sourceKPFiniteTranslateLevel_le_conjugate_one K hζ T)))

theorem sourceKPTranslateCompactHaar_eq_of_domain (E : Set XJ)
    (hE : IsFundamentalDomain Γ E νJ) :
    sourceKPTranslateCompactHaar K hζ T = Measure.map qJ ((νJ).restrict E) := by
  let : Countable Γ := sourceKPCuspRationalProjective_countable K
  have hq := sourceKPTranslateRepresentativeToCompact_measurable K hζ T
  ext U hU
  simp only [sourceKPTranslateCompactHaar, Measure.map_apply hq hU,
    Measure.restrict_apply (hU.preimage hq)]
  apply (sourceKPTranslateRepresentativeDomain_isFundamental K hζ T 1
    (sourceKPFiniteTranslateLevel_le_conjugate_one K hζ T)).measure_set_eq hE (hU.preimage hq)
  intro γ
  ext x
  change qJ (γ • x) ∈ U ↔ qJ x ∈ U
  rw [sourceKPTranslateRepresentativeToCompact_rational]

theorem sourceKPTranslateAutomorphicCompactMap_haar (t : Gf) (h : J ≤ D t) :
    Measure.map (sourceKPTranslateAutomorphicCompactMap K hζ T t h)
      (sourceKPTranslateCompactHaar K hζ T) =
        ((J).relIndex (D t) : ℝ≥0∞) • μY := by
  have hp := (sourceKPTranslateAutomorphicCompactMap_continuous K hζ T t h).measurable
  have hqJ := sourceKPTranslateRepresentativeToCompact_measurable K hζ T
  have hf := sourceKPTranslateRepresentativeMap_measurable K hζ T t h
  have hq := sourceKPFiniteLevelToCompact_measurable K hζ
  rw [sourceKPTranslateCompactHaar_eq_of_domain K hζ T _
      (sourceKPTranslateRepresentativeDomain_isFundamental K hζ T t h),
    Measure.map_map hp hqJ, sourceKPTranslateCompactMap_comp_representative,
    ← Measure.map_map hq hf, sourceKPTranslateRepresentativeDomain,
    ← Measure.restrict_map hf (sourceKPTranslateBaseDomain_measurable K hζ),
    sourceKPTranslateRepresentativeMap_haar, Measure.restrict_smul,
    Measure.map_smul _ hq.aemeasurable, sourceKPTranslateBaseHaar_map]

theorem sourceKPTranslateAutomorphicCompactMap_quasiMeasurePreserving (t : Gf) (h : J ≤ D t) :
    Measure.QuasiMeasurePreserving (sourceKPTranslateAutomorphicCompactMap K hζ T t h)
      (sourceKPTranslateCompactHaar K hζ T) μY := by
  refine ⟨(sourceKPTranslateAutomorphicCompactMap_continuous K hζ T t h).measurable, ?_⟩
  intro S hS
  rw [sourceKPTranslateAutomorphicCompactMap_haar, Measure.smul_apply, hS, smul_zero]

end
end ArtinMatthews
