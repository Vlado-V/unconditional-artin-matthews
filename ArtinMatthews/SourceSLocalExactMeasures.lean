module

public import ArtinMatthews.SourceSLocalProductDisintegration
public import ArtinMatthews.SourceLocalMultiplicativeHaar
public import ArtinMatthews.SourceSheetProfile


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory Topology
open scoped NumberField Classical ENNReal
noncomputable section

variable {K : Type} [Field K] [NumberField K]

scoped instance sourceArchCompletionMeasurableSpace (w : InfinitePlace K) :
    MeasurableSpace w.Completion := borel _

scoped instance sourceArchCompletionBorelSpace (w : InfinitePlace K) :
    BorelSpace w.Completion := ⟨rfl⟩

scoped instance sourceArchCompletionUnitsBorelSpace (w : InfinitePlace K) :
    BorelSpace w.Completionˣ := sourceComplexPlaceUnits_borel (v := w)

variable (K)
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- The archimedean factors carry the actual trace-self-dual multiplicative Haar. -/
def sourceSLocalArchUnitMeasure (w : InfinitePlace K) : Measure w.Completionˣ :=
  sourceComplexPlaceUnitHaar ((source_isTotallyComplex K hζ).isComplex w)

def sourceSLocalFiniteUnitMeasure (p : S) : Measure (p.val.adicCompletion K)ˣ :=
  sourceLocalMulMeasure K p.val

scoped instance sourceSLocalArchUnitMeasure_isHaar (w : InfinitePlace K) :
    (sourceSLocalArchUnitMeasure K hζ w).IsHaarMeasure :=
  sourceComplexPlaceUnitHaar_isHaar _

scoped instance sourceSLocalFiniteUnitMeasure_isHaar (p : S) :
    (sourceSLocalFiniteUnitMeasure K S p).IsHaarMeasure :=
  sourceLocalMulMeasure_isHaar K p.val

scoped instance sourceComplexUnitHaar_sigmaFinite : SigmaFinite sourceComplexUnitHaar :=
  sourceComplexUnitPolarHomeomorph.toMeasurableEquiv.sigmaFinite_map

scoped instance sourceSLocalArchUnitMeasure_sigmaFinite (w : InfinitePlace K) :
    SigmaFinite (sourceSLocalArchUnitMeasure K hζ w) := by
  let e := (sourceComplexPlaceUnitsEquiv ((source_isTotallyComplex K hζ).isComplex w)).symm.toHomeomorph
  exact e.toMeasurableEquiv.sigmaFinite_map

scoped instance sourceSLocalFiniteUnitMeasure_sigmaFinite (p : S) :
    SigmaFinite (sourceSLocalFiniteUnitMeasure K S p) := by
  have : (sourceLocalMulMeasure K p.val).IsHaarMeasure := sourceLocalMulMeasure_isHaar K p.val
  have h : IsOpenEmbedding (Units.val : (p.val.adicCompletion K)ˣ → p.val.adicCompletion K) :=
    IsOpenUnits.isOpenEmbedding_unitsVal
  let : PolishSpace (Set.range (Units.val : (p.val.adicCompletion K)ˣ → p.val.adicCompletion K)) :=
    h.isOpen_range.polishSpace
  let : PolishSpace (p.val.adicCompletion K)ˣ := h.isEmbedding.toHomeomorph.isClosedEmbedding.polishSpace
  let : LocallyCompactSpace (p.val.adicCompletion K)ˣ := h.locallyCompactSpace
  unfold sourceSLocalFiniteUnitMeasure
  infer_instance

def sourceSLocalUnitProductMeasure : Measure (SWholeUnits K S) :=
  (Measure.pi (sourceSLocalArchUnitMeasure K hζ)).prod
    (Measure.pi (sourceSLocalFiniteUnitMeasure K S))

variable (v : InfinitePlace K)

def sourceSLocalOtherUnitMeasure : Measure (SNormOneOtherUnits S v) :=
  sourceSheetOtherMeasure S v (sourceSLocalArchUnitMeasure K hζ) (sourceSLocalFiniteUnitMeasure K S)

def sourceSLocalNormalizedSheetMeasure : Measure (SNormOne K S) :=
  sourceSNormOneSheetMeasure S ((source_isTotallyComplex K hζ).isComplex v)
    (sourceCircleHaar.prod (sourceSLocalOtherUnitMeasure K hζ S v))

theorem sourceSLocalArchUnitMeasure_eq_polar :
    sourceSLocalArchUnitMeasure K hζ v =
      Measure.map (sourceSLocalPolarPlace ((source_isTotallyComplex K hζ).isComplex v))
        (sourceCircleHaar.prod sourceRealLogHaar) := by
  let hv := (source_isTotallyComplex K hζ).isComplex v
  unfold sourceSLocalArchUnitMeasure sourceComplexPlaceUnitHaar sourceComplexUnitHaar
  rw [Measure.map_map (show Measurable ((sourceComplexPlaceUnitsEquiv hv).symm : ℂˣ → v.Completionˣ) from
    (sourceComplexPlaceUnitsEquiv hv).symm.continuous.measurable)
    (show Measurable (sourceComplexUnitPolarMulEquiv : Circle × Multiplicative ℝ → ℂˣ) from
      sourceComplexUnitPolarHomeomorph.continuous.measurable)]
  rfl

theorem sourceSLocalUnitProductMeasure_eq_radial :
    let : BorelSpace (SWholeUnits K S) := sourceSWholeUnits_product_borel S v
    sourceSLocalUnitProductMeasure K hζ S =
      sourceSLocalRadialHaar S ((source_isTotallyComplex K hζ).isComplex v)
        (sourceSLocalNormalizedSheetMeasure K hζ S v) := by
  exact sourceSLocalProductMeasure_eq_radial S ((source_isTotallyComplex K hζ).isComplex v)
    (sourceSLocalArchUnitMeasure K hζ) (sourceSLocalFiniteUnitMeasure K S)
    (sourceSLocalArchUnitMeasure_eq_polar K hζ v)

end
end ArtinMatthews.SourcePhysical
