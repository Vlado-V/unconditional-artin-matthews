module

public import ArtinMatthews.SourceKPArchMeasureTopology
public import ArtinMatthews.SourceLeftFundamentalDomain


set_option backward.privateInPublic true
@[expose] public section

/-! A measurable left arithmetic fundamental domain and its quotient measure. -/
namespace ArtinMatthews
open NumberField Matrix MeasureTheory Set
open scoped NumberField MatrixGroups AdeleRing Classical ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)


instance sourceKPArchComponentQuotient_opensMeasurable
    (b : SourceKPFiniteLevelFiber K hζ) :
    OpensMeasurableSpace (SourceKPArchComponentQuotient K hζ b) where
  borel_le := by
    apply MeasurableSpace.generateFrom_le
    intro U hU
    apply measurableSet_quotient.mpr
    exact (hU.preimage (sourceKPArchComponentQuotientMap_continuous K hζ b)).measurableSet

theorem sourceKPArchComponent_exists_fundamentalDomain_subset
    (b : SourceKPFiniteLevelFiber K hζ)
    (μ : Measure (PGL(2, InfiniteAdeleRing K)))
    (D : Set (PGL(2, InfiniteAdeleRing K))) (hD : MeasurableSet D)
    (hcover : ∀ g, ∃ γ : sourceKPArchComponentSubgroup K hζ b, γ • g ∈ D) :
    ∃ F ⊆ D, MeasurableSet F ∧
      IsFundamentalDomain (sourceKPArchComponentSubgroup K hζ b) F μ :=
  sourceLeftFundamentalDomain_exists_subset (sourceKPArchComponentSubgroup K hζ b) μ D hD hcover

def sourceKPArchComponentFundamentalDomain (b : SourceKPFiniteLevelFiber K hζ)
    (μ : Measure (PGL(2, InfiniteAdeleRing K))) : Set (PGL(2, InfiniteAdeleRing K)) :=
  Classical.choose (sourceLeftFundamentalDomain_exists (sourceKPArchComponentSubgroup K hζ b) μ)

theorem sourceKPArchComponentFundamentalDomain_measurable
    (b : SourceKPFiniteLevelFiber K hζ) (μ : Measure (PGL(2, InfiniteAdeleRing K))) :
    MeasurableSet (sourceKPArchComponentFundamentalDomain K hζ b μ) :=
  (Classical.choose_spec (sourceLeftFundamentalDomain_exists
    (sourceKPArchComponentSubgroup K hζ b) μ)).1

theorem sourceKPArchComponentFundamentalDomain_isFundamental
    (b : SourceKPFiniteLevelFiber K hζ) (μ : Measure (PGL(2, InfiniteAdeleRing K))) :
    IsFundamentalDomain (sourceKPArchComponentSubgroup K hζ b)
      (sourceKPArchComponentFundamentalDomain K hζ b μ) μ :=
  (Classical.choose_spec (sourceLeftFundamentalDomain_exists
    (sourceKPArchComponentSubgroup K hζ b) μ)).2

instance sourceKPArchComponent_hasFundamentalDomain
    (b : SourceKPFiniteLevelFiber K hζ) (μ : Measure (PGL(2, InfiniteAdeleRing K))) :
    HasFundamentalDomain (sourceKPArchComponentSubgroup K hζ b)
      (PGL(2, InfiniteAdeleRing K)) μ :=
  (sourceKPArchComponentFundamentalDomain_isFundamental K hζ b μ).hasFundamentalDomain μ

def sourceKPArchComponentQuotientMeasure (b : SourceKPFiniteLevelFiber K hζ)
    (μ : Measure (PGL(2, InfiniteAdeleRing K))) :
    Measure (SourceKPArchComponentQuotient K hζ b) :=
  (μ.restrict (sourceKPArchComponentFundamentalDomain K hζ b μ)).map
    (sourceKPArchComponentQuotientMap K hζ b)

variable (b : SourceKPFiniteLevelFiber K hζ) (μ : Measure (PGL(2, InfiniteAdeleRing K)))
    [μ.IsMulLeftInvariant]

theorem sourceKPArchComponentQuotientMeasure_independent
    (D : Set (PGL(2, InfiniteAdeleRing K)))
    (hD : IsFundamentalDomain (sourceKPArchComponentSubgroup K hζ b) D μ) :
    sourceKPArchComponentQuotientMeasure K hζ b μ =
      (μ.restrict D).map (sourceKPArchComponentQuotientMap K hζ b) := by
  exact (sourceKPArchComponentFundamentalDomain_isFundamental K hζ b μ).quotientMeasure_eq μ hD

instance sourceKPArchComponent_quotientMeasureEqMeasurePreimage :
    QuotientMeasureEqMeasurePreimage (G := sourceKPArchComponentSubgroup K hζ b)
      μ (sourceKPArchComponentQuotientMeasure K hζ b μ) :=
  (sourceKPArchComponentFundamentalDomain_isFundamental K hζ b μ).quotientMeasureEqMeasurePreimage_quotientMeasure

theorem sourceKPArchComponentQuotientMeasure_apply
    (D : Set (PGL(2, InfiniteAdeleRing K)))
    (hD : IsFundamentalDomain (sourceKPArchComponentSubgroup K hζ b) D μ)
    (U : Set (SourceKPArchComponentQuotient K hζ b)) (hU : MeasurableSet U) :
    sourceKPArchComponentQuotientMeasure K hζ b μ U =
      μ ((sourceKPArchComponentQuotientMap K hζ b) ⁻¹' U ∩ D) :=
  hD.projection_respects_measure_apply (sourceKPArchComponentQuotientMeasure K hζ b μ) hU

theorem sourceKPArchComponentQuotientMap_measurePreserving
    (D : Set (PGL(2, InfiniteAdeleRing K)))
    (hD : IsFundamentalDomain (sourceKPArchComponentSubgroup K hζ b) D μ) :
    MeasurePreserving (sourceKPArchComponentQuotientMap K hζ b)
      (μ.restrict D) (sourceKPArchComponentQuotientMeasure K hζ b μ) :=
  hD.measurePreserving_quotient_mk (sourceKPArchComponentQuotientMeasure K hζ b μ)

theorem sourceKPArchComponentQuotientMeasure_unique
    (ν : Measure (SourceKPArchComponentQuotient K hζ b))
    [QuotientMeasureEqMeasurePreimage (G := sourceKPArchComponentSubgroup K hζ b) μ ν] :
    ν = sourceKPArchComponentQuotientMeasure K hζ b μ :=
  QuotientMeasureEqMeasurePreimage.unique
    (G := sourceKPArchComponentSubgroup K hζ b) (ν := μ)
    ν (sourceKPArchComponentQuotientMeasure K hζ b μ)

omit [μ.IsMulLeftInvariant] in
theorem sourceKPArchComponentQuotientMeasure_univ :
    sourceKPArchComponentQuotientMeasure K hζ b μ Set.univ =
      μ (sourceKPArchComponentFundamentalDomain K hζ b μ) := by
  rw [sourceKPArchComponentQuotientMeasure,
    Measure.map_apply (sourceKPArchComponentQuotientMap_measurable K hζ b) MeasurableSet.univ]
  simp

theorem sourceKPArchComponentQuotientMeasure_univ_ne_zero (hμ : μ ≠ 0) :
    sourceKPArchComponentQuotientMeasure K hζ b μ Set.univ ≠ 0 := by
  rw [sourceKPArchComponentQuotientMeasure_univ K hζ b μ]
  exact (sourceKPArchComponentFundamentalDomain_isFundamental K hζ b μ).measure_ne_zero hμ

instance sourceKPArchComponentQuotientMeasure_sigmaFinite [SigmaFinite μ] :
    SigmaFinite (sourceKPArchComponentQuotientMeasure K hζ b μ) :=
  QuotientMeasureEqMeasurePreimage.sigmaFiniteQuotient
    (G := sourceKPArchComponentSubgroup K hζ b) (ν := μ)
    (sourceKPArchComponentQuotientMeasure K hζ b μ)

end
end ArtinMatthews
