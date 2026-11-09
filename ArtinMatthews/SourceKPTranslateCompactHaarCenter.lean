module

public import ArtinMatthews.SourceKPTranslateCompactCenter
public import ArtinMatthews.SourceKPTranslateCompactHaar


set_option backward.privateInPublic true
@[expose] public section

/-! Cubic invariance of the actual common-level Haar measure. -/
namespace ArtinMatthews
open NumberField Matrix Topology MeasureTheory
open scoped NumberField MatrixGroups AdeleRing ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Γ" => PGL(2, K)
local notation "Z" => rootsOfUnity 3 K
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "D" => sourceKPFiniteLevelConjugate K hζ
local notation "c" => sourceKPFiniteAdeleProjectiveCenter K hζ

variable (T : Finset (SourceKPFiniteAdeleProjective K hζ))
include T

local notation "J" => sourceKPFiniteTranslateLevel K hζ T
local notation "XJ" => SourceKPTranslateRepresentativeSpace K hζ T
local notation "YJ" => SourceKPTranslateAutomorphicCompactLevel K hζ T
local notation "qJ" => sourceKPTranslateRepresentativeToCompact K hζ T
local notation "νJ" => sourceKPTranslateRepresentativeHaar K hζ T
local notation "μJ" => sourceKPTranslateCompactHaar K hζ T

private def representativeCenter (z : Z) : XJ → XJ :=
  Prod.map id (fun b => c z • b)

theorem sourceKPTranslateCompactHaar_center_preserving (z : Z) :
    MeasurePreserving (fun y : YJ => z • y) μJ μJ := by
  let C := representativeCenter K hζ T z
  let E := sourceKPTranslateRepresentativeDomain K hζ T 1
    (sourceKPFiniteTranslateLevel_le_conjugate_one K hζ T)
  have hmp : MeasurePreserving C νJ νJ :=
    (MeasurePreserving.id (sourceKPArchHaar K hζ)).prod
      (sourceKPTranslateFiniteCount_preserving K hζ T (c z))
  have hE : IsFundamentalDomain Γ E νJ :=
    sourceKPTranslateRepresentativeDomain_isFundamental K hζ T 1
      (sourceKPFiniteTranslateLevel_le_conjugate_one K hζ T)
  have hEm : MeasurableSet E := sourceKPTranslateRepresentativeDomain_measurable K hζ T 1
    (sourceKPFiniteTranslateLevel_le_conjugate_one K hζ T)
  have hEC : IsFundamentalDomain Γ (C ⁻¹' E) νJ := by
    apply hE.preimage_of_equiv hmp.quasiMeasurePreserving Function.bijective_id
    intro γ x
    apply Prod.ext
    · rfl
    · change c z • (sourceKPRationalFiniteMap K hζ γ • x.2) =
        sourceKPRationalFiniteMap K hζ γ • (c z • x.2)
      rw [smul_smul, smul_smul,
        (sourceKPFiniteAdeleProjectiveCenter_commute K hζ z (sourceKPRationalFiniteMap K hζ γ)).eq]
  have hq := sourceKPTranslateRepresentativeToCompact_measurable K hζ T
  have hz : Measurable (fun y : YJ => z • y) := (continuous_const_smul z).measurable
  have he : (fun y : YJ => z • y) ∘ qJ = qJ ∘ C := rfl
  refine ⟨hz, ?_⟩
  conv_lhs => rw [sourceKPTranslateCompactHaar_eq_of_domain K hζ T _ hEC]
  rw [Measure.map_map hz hq, he, ← Measure.map_map hq hmp.measurable,
    ← Measure.restrict_map hmp.measurable hEm, hmp.map_eq] <;> rfl

end
end ArtinMatthews
