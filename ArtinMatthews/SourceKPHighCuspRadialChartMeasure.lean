module

public import ArtinMatthews.SourceKPHighCuspMeasure


set_option backward.privateInPublic true
@[expose] public section

/-! Radial measure transport on injective full-frame high-cusp charts. -/
namespace ArtinMatthews
open NumberField Matrix Topology MeasureTheory Set
open scoped NumberField MatrixGroups AdeleRing ENNReal
noncomputable section
variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPHighCuspRadial_measure_chart (t T : ℝ) (hT : 1 < T)
    (htT : 1 < sourceKPRadialHeightScale K t*T)
    (b : SourceKPFiniteLevelFiber K hζ)
    (U : Set (PGL(2, InfiniteAdeleRing K))) (hU : MeasurableSet U)
    (hhigh : ∀ g ∈ U, T < sourceKPFiniteLevelHeight K hζ (g,b))
    (hinj : Set.InjOn (sourceKPArchComponentPoint K hζ b) U)
    (A : Set (SourceKPHighCuspAutomorphic K hζ (sourceKPRadialHeightScale K t*T)))
    (hA : MeasurableSet A)
    (hcover : Subtype.val '' A ⊆
      (fun g => sourceKPArchComponentPoint K hζ b (sourceKPArchRadialFlow K hζ t g)) '' U) :
    sourceKPHighCuspMeasure K hζ T
      ((sourceKPHighCuspRadialHomeomorph K hζ t T hT htT) ⁻¹' A) =
      ENNReal.ofReal (sourceKPRadialHeightScale K t) *
        sourceKPHighCuspMeasure K hζ (sourceKPRadialHeightScale K t*T) A := by
  let F := sourceKPArchRadialHomeomorph K hζ t
  let e := sourceKPHighCuspRadialHomeomorph K hζ t T hT htT
  let j := sourceKPArchComponentPoint K hζ b
  let E := U ∩ (fun g => j (F g)) ⁻¹' (Subtype.val '' A)
  have hvalA : MeasurableSet (Subtype.val '' A) :=
    (MeasurableEmbedding.subtype_coe
      (sourceKPHighCuspAutomorphic_isOpen K hζ _).measurableSet).measurableSet_image.mpr hA
  have hE : MeasurableSet E := hU.inter (hvalA.preimage
    ((sourceKPArchComponentPoint_continuous K hζ b).comp F.continuous).measurable)
  let lift : ∀ g ∈ U, SourceKPHighCuspAutomorphic K hζ T := fun g hg =>
    sourceKPHighCuspProjection K hζ T ⟨(g,b),hhigh g hg⟩
  have hlift (g) (hg : g ∈ U) : (lift g hg).val = j g := rfl
  have hrep (g) (hg : g ∈ U) : (e (lift g hg)).val = j (F g) :=
    congrArg Subtype.val (sourceKPHighCuspRadialHomeomorph_rep K hζ t T hT htT
      ⟨(g,b),hhigh g hg⟩)
  have hsimage : Subtype.val '' (e ⁻¹' A) = j '' E := by
    ext x
    constructor
    · rintro ⟨q,hq,rfl⟩
      obtain ⟨g,hg,hgq⟩ := hcover ⟨e q,hq,rfl⟩
      have heq : e (lift g hg) = e q := Subtype.ext ((hrep g hg).trans hgq)
      have hqg := e.injective heq
      refine ⟨g,⟨hg,⟨e q,hq,hgq.symm⟩⟩,?_⟩
      exact (hlift g hg).symm.trans (congrArg Subtype.val hqg)
    · rintro ⟨g,⟨hg,hh⟩,rfl⟩
      obtain ⟨q,hq,hqg⟩ := hh
      have heq : e (lift g hg) = q := Subtype.ext ((hrep g hg).trans hqg.symm)
      refine ⟨lift g hg,?_,hlift g hg⟩
      change e (lift g hg) ∈ A
      rw [heq]
      exact hq
  have htimage : Subtype.val '' A = j '' (F '' E) := by
    ext x
    constructor
    · rintro ⟨q,hq,rfl⟩
      obtain ⟨g,hg,hgq⟩ := hcover ⟨q,hq,rfl⟩
      exact ⟨F g,⟨g,⟨hg,⟨q,hq,hgq.symm⟩⟩,rfl⟩,hgq⟩
    · rintro ⟨_,⟨g,hg,rfl⟩,rfl⟩
      exact hg.2
  have hFinj : Set.InjOn j (F '' E) := by
    rintro _ ⟨g,hg,rfl⟩ _ ⟨g',hg',rfl⟩ heq
    have he : e (lift g hg.1) = e (lift g' hg'.1) :=
      Subtype.ext ((hrep g hg.1).trans (heq.trans (hrep g' hg'.1).symm))
    have hj : j g = j g' := by
      exact (hlift g hg.1).symm.trans ((congrArg Subtype.val (e.injective he)).trans (hlift g' hg'.1))
    exact congrArg F (hinj hg.1 hg'.1 hj)
  have hFE : MeasurableSet (F '' E) := F.measurableEmbedding.measurableSet_image.mpr hE
  have hm := congrArg (fun μ : Measure (PGL(2, InfiniteAdeleRing K)) => μ (F '' E))
    (sourceKPArchRadialFlow_map_haar K hζ t)
  change (Measure.map F (sourceKPArchHaar K hζ)) (F '' E) =
    (ENNReal.ofReal (sourceKPRadialHeightScale K t) • sourceKPArchHaar K hζ) (F '' E) at hm
  rw [Measure.map_apply F.measurable hFE, Set.preimage_image_eq _ F.injective,
    Measure.smul_apply] at hm
  rw [sourceKPHighCuspMeasure_apply, hsimage,
    sourceKPAutomorphicMeasure_injective_chart K hζ (sourceKPArchHaar K hζ) b E hE
      (hinj.mono Set.inter_subset_left), sourceKPHighCuspMeasure_apply, htimage,
    sourceKPAutomorphicMeasure_injective_chart K hζ (sourceKPArchHaar K hζ) b (F '' E) hFE hFinj]
  exact hm

end
end ArtinMatthews
