module

public import ArtinMatthews.SourceKPTranslateBaseDomain
public import ArtinMatthews.SourceKPAutomorphicParametricContinuity
public import ArtinMatthews.SourceKPAutomorphicL2


set_option backward.privateInPublic true
@[expose] public section

/-! Restricting the actual representative Haar measure to the base domain
recovers the canonical compact automorphic Haar measure. -/
namespace ArtinMatthews
open NumberField Matrix Topology MeasureTheory Set
open scoped NumberField MatrixGroups AdeleRing ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "A" => PGL(2, InfiniteAdeleRing K)
local notation "F" => SourceKPFiniteLevelFiber K hζ
local notation "X" => SourceKPFiniteLevelSpace K hζ
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "I" => SourceKPFiniteOrbit K hζ
local notation "b" => sourceKPFiniteOrbitRepresentative K hζ
local notation "q" => sourceKPFiniteLevelToCompact K hζ
local notation "D" => sourceKPTranslateBaseDomain K hζ
local notation "μA" => sourceKPArchHaar K hζ
local notation "μX" => sourceKPFiniteRepresentativeHaar K hζ
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)

theorem sourceKPFiniteLevelToCompact_measurable : Measurable q := by
  let : SecondCountableTopology F := DiscreteTopology.secondCountableTopology_of_countable
  exact (sourceKPFiniteLevelToCompact_isOpenQuotientMap K hζ).continuous.measurable

theorem sourceKPTranslateBaseHaar_map : Measure.map q ((μX).restrict D) = μY := by
  let f (U : Set Y) (v : F) : ℝ≥0∞ := μA {a : A | (a,v) ∈ q ⁻¹' U ∩ D}
  have hb : Function.Injective b := by
    intro i j h
    have he := congrArg (sourceKPFiniteOrbitMk K hζ) h
    simpa only [sourceKPFiniteOrbitRepresentative_spec] using he
  have hsupp (U : Set Y) : Function.support (f U) ⊆ Set.range b := by
    intro v hv
    by_contra h
    have he : {a : A | (a,v) ∈ q ⁻¹' U ∩ D} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro a ha
      obtain ⟨i, hi, _⟩ := (sourceKPTranslateBaseDomain_mem K hζ (a,v)).mp ha.2
      exact h ⟨i,hi.symm⟩
    apply hv
    change μA {a : A | (a,v) ∈ q ⁻¹' U ∩ D} = 0
    rw [he, measure_empty]
  have hslice (U : Set Y) (i : I) :
      {a : A | (a,b i) ∈ q ⁻¹' U ∩ D} =
        (fun a : A => q (a,b i)) ⁻¹' U ∩ sourceKPTranslateBaseSlice K hζ i := by
    ext a
    constructor
    · rintro ⟨ha, hd⟩
      obtain ⟨j, hij, haj⟩ := (sourceKPTranslateBaseDomain_mem K hζ (a,b i)).mp hd
      have he : i = j := hb hij
      exact ⟨ha, he.symm ▸ haj⟩
    · rintro ⟨ha, hd⟩
      exact ⟨ha, (sourceKPTranslateBaseDomain_mem K hζ (a,b i)).mpr ⟨i,rfl,hd⟩⟩
  ext U hU
  have hq := sourceKPFiniteLevelToCompact_measurable K hζ
  rw [Measure.map_apply hq hU, Measure.restrict_apply (hU.preimage hq),
    sourceKPFiniteRepresentativeHaar_apply K hζ _
      ((hU.preimage hq).inter (sourceKPTranslateBaseDomain_measurable K hζ))]
  change (∑' v : F, f U v) = μY U
  rw [← hb.tsum_eq (hsupp U), sourceKPAutomorphicCompactMeasure,
    Measure.map_apply (sourceKPAutomorphicCompactMk_measurable K hζ) hU,
    sourceKPAutomorphicMeasure_apply K hζ μA _
      (hU.preimage (sourceKPAutomorphicCompactMk_measurable K hζ))]
  apply tsum_congr
  intro i
  change μA {a : A | (a,b i) ∈ q ⁻¹' U ∩ D} = _
  rw [hslice, sourceKPArchComponentQuotientMeasure_apply K hζ (b i) μA
    (sourceKPTranslateBaseSlice K hζ i) (sourceKPTranslateBaseSlice_isFundamental K hζ i μA) _
    ((hU.preimage (sourceKPAutomorphicCompactMk_measurable K hζ)).preimage
      (sourceKPArchComponentEmbedding_measurable K hζ (b i)))] <;> rfl

end
end ArtinMatthews
