module

public import ArtinMatthews.SourceKPCuspFundamentalSection


set_option backward.privateInPublic true
@[expose] public section

/-! The selected high representatives carry exactly the original automorphic
measure. Each finite fiber is counted once and uses the actual archimedean Haar. -/
namespace ArtinMatthews
open NumberField Matrix Topology MeasureTheory Set Function
open scoped NumberField MatrixGroups AdeleRing ENNReal

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPCuspHighSection_measurePreserving (T : ℝ)
    (F : Set (SourceKPHighCuspFinite K hζ T)) (hF : MeasurableSet F)
    (hinj : Set.InjOn (sourceKPHighCuspProjection K hζ T) F)
    (hcover : sourceKPHighCuspProjection K hζ T '' F = Set.univ) :
    MeasurePreserving (sourceKPHighCuspProjection K hζ T)
      ((sourceKPHighRepresentativeHaar K hζ T).restrict F)
      (sourceKPHighCuspMeasure K hζ T) := by
  let X := SourceKPHighCuspFinite K hζ T
  let p := sourceKPHighCuspProjection K hζ T
  have hp : Measurable p := (sourceKPCuspHighProjection_continuous K hζ T).measurable
  refine ⟨hp, ?_⟩
  ext V hV
  let U : Set X := p ⁻¹' V ∩ F
  have hU : MeasurableSet U := (hV.preimage hp).inter hF
  have hval := MeasurableEmbedding.subtype_coe
    (sourceKPHighRepresentative_isOpen K hζ T).measurableSet
  have hUv : MeasurableSet (Subtype.val '' U) := hval.measurableSet_image.mpr hU
  let A (b : SourceKPFiniteLevelFiber K hζ) : Set (PGL(2, InfiniteAdeleRing K)) :=
    {a | (a,b) ∈ Subtype.val '' U}
  let W (b : SourceKPFiniteLevelFiber K hζ) :=
    sourceKPArchComponentPoint K hζ b '' A b
  have hA (b : SourceKPFiniteLevelFiber K hζ) : MeasurableSet (A b) :=
    hUv.preimage (continuous_id.prodMk continuous_const).measurable
  have hmatch {b : SourceKPFiniteLevelFiber K hζ} {a : PGL(2, InfiniteAdeleRing K)}
      {x : X} (hx : x.val = (a,b)) :
      (p x).val = sourceKPArchComponentPoint K hζ b a :=
    congrArg (Quotient.mk _) hx
  have hInj (b : SourceKPFiniteLevelFiber K hζ) :
      Set.InjOn (sourceKPArchComponentPoint K hζ b) (A b) := by
    rintro a ⟨x,hx,hax⟩ c ⟨y,hy,hcy⟩ he
    have hpxy : p x = p y :=
      Subtype.ext ((hmatch hax).trans (he.trans (hmatch hcy).symm))
    have hxy := hinj hx.2 hy.2 hpxy
    exact congrArg Prod.fst (hax.symm.trans ((congrArg Subtype.val hxy).trans hcy))
  have hW (b : SourceKPFiniteLevelFiber K hζ) : MeasurableSet (W b) :=
    (hA b).image_of_continuousOn_injOn
      (sourceKPArchComponentPoint_continuous K hζ b).continuousOn (hInj b)
  have hWdisj : Pairwise (Disjoint on W) := by
    intro b c hbc
    apply Set.disjoint_left.mpr
    rintro z ⟨a,⟨x,hx,hax⟩,haz⟩ ⟨d,⟨y,hy,hdy⟩,hdz⟩
    have hpxy : p x = p y :=
      Subtype.ext ((hmatch hax).trans (haz.trans (hdz.symm.trans (hmatch hdy).symm)))
    have hxy := hinj hx.2 hy.2 hpxy
    exact hbc (congrArg Prod.snd (hax.symm.trans ((congrArg Subtype.val hxy).trans hdy)))
  have hVU : Subtype.val '' V = ⋃ b, W b := by
    ext z
    constructor
    · rintro ⟨q,hq,rfl⟩
      have hqF : q ∈ p '' F := by
        change q ∈ sourceKPHighCuspProjection K hζ T '' F
        rw [hcover]
        trivial
      obtain ⟨x,hx,hpx⟩ := hqF
      have hxV : p x ∈ V := by rwa [hpx]
      refine Set.mem_iUnion.mpr ⟨x.val.2,x.val.1,?_,?_⟩
      · exact ⟨x,⟨hxV,hx⟩,rfl⟩
      · exact congrArg Subtype.val hpx
    · intro hz
      obtain ⟨b,a,⟨x,hx,hax⟩,rfl⟩ := Set.mem_iUnion.mp hz
      exact ⟨p x,hx.1,hmatch hax⟩
  rw [Measure.map_apply hp hV, Measure.restrict_apply (hV.preimage hp)]
  change sourceKPHighRepresentativeHaar K hζ T U = sourceKPHighCuspMeasure K hζ T V
  rw [sourceKPHighRepresentativeHaar_apply, sourceKPFiniteRepresentativeHaar_apply K hζ _ hUv,
    sourceKPHighCuspMeasure_apply, hVU, measure_iUnion hWdisj hW]
  apply tsum_congr
  intro b
  exact (sourceKPAutomorphicMeasure_injective_chart K hζ (sourceKPArchHaar K hζ)
    b (A b) (hA b) (hInj b)).symm

end
end ArtinMatthews
