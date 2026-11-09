module

public import ArtinMatthews.SourceArchHyperbolicRegularity
public import ArtinMatthews.SourceArchHyperbolicEuclidean
public import ArtinMatthews.SourceKPArchUpperAction


set_option backward.privateInPublic true
@[expose] public section

/-! The invariant regular product measure on the actual archimedean symmetric quotient. -/
namespace ArtinMatthews
open NumberField Matrix Matrix.GeneralLinearGroup SourceArchJacquet MeasureTheory MeasureTheory.Measure
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPArchHyperbolicMeasure : Measure (SourceKPArchUpperHalfSpace K) :=
  Measure.pi (fun _ : InfinitePlace K => sourceArchHyperbolicMeasure)

instance sourceKPArchHyperbolicMeasure_sigmaFinite : SigmaFinite (sourceKPArchHyperbolicMeasure K) := by
  unfold sourceKPArchHyperbolicMeasure
  infer_instance

instance sourceKPArchHyperbolicMeasure_finiteOnCompacts :
    IsFiniteMeasureOnCompacts (sourceKPArchHyperbolicMeasure K) := by
  unfold sourceKPArchHyperbolicMeasure
  infer_instance

instance sourceKPArchHyperbolicMeasure_openPos : IsOpenPosMeasure (sourceKPArchHyperbolicMeasure K) := by
  unfold sourceKPArchHyperbolicMeasure
  infer_instance

lemma sourceKPArchHyperbolicMeasure_sFinite : SFinite (sourceKPArchHyperbolicMeasure K) := inferInstance

lemma sourceKPArchUpperAction_preserving (a : PGL(2, InfiniteAdeleRing K)) :
    MeasurePreserving (sourceKPArchUpperAction K hζ a)
      (sourceKPArchHyperbolicMeasure K) (sourceKPArchHyperbolicMeasure K) :=
  measurePreserving_pi (fun _ : InfinitePlace K => sourceArchHyperbolicMeasure)
    (fun _ : InfinitePlace K => sourceArchHyperbolicMeasure)
    (fun v => sourceArchHyperbolicMeasure_preserving (sourceKPArchProjectiveAt K hζ v a))

def sourceKPArchEuclideanUpperMap
    (p : InfinitePlace K → OAI.CubicEisenstein.EuclideanSpatial) : SourceKPArchUpperHalfSpace K :=
  fun v => sourceArchEuclideanUpperMap (p v)

lemma sourceKPArchEuclideanUpperMap_preserving :
    MeasurePreserving (sourceKPArchEuclideanUpperMap K)
      (Measure.pi (fun _ : InfinitePlace K => OAI.CubicEisenstein.hyperbolicEuclideanVolume))
      (sourceKPArchHyperbolicMeasure K) :=
  measurePreserving_pi (fun _ : InfinitePlace K => OAI.CubicEisenstein.hyperbolicEuclideanVolume)
    (fun _ : InfinitePlace K => sourceArchHyperbolicMeasure)
    (fun _ => sourceArchEuclideanUpperMap_preserving)

omit [NumberField K] in
lemma sourceKPArchEuclideanUpperMap_positive
    (p : InfinitePlace K → OAI.CubicEisenstein.EuclideanSpatial)
    (hp : ∀ v, 0 < p v 2) (v : InfinitePlace K) :
    sourceKPArchEuclideanUpperMap K p v =
      ((p v 0 : ℂ) + Complex.I * (p v 1 : ℂ), ⟨p v 2, hp v⟩) :=
  sourceArchEuclideanUpperMap_positive (p v) (hp v)

def sourceKPArchUpperEuclideanMap (p : SourceKPArchUpperHalfSpace K) :
    InfinitePlace K → OAI.CubicEisenstein.EuclideanSpatial :=
  fun v => sourceArchUpperEuclideanMap (p v)

omit [NumberField K] in
lemma sourceKPArchUpperEuclideanMap_continuous : Continuous (sourceKPArchUpperEuclideanMap K) :=
  continuous_pi (fun v => sourceArchUpperEuclideanMap_continuous.comp (continuous_apply v))

lemma sourceKPArchUpperEuclideanMap_preserving :
    MeasurePreserving (sourceKPArchUpperEuclideanMap K)
      (sourceKPArchHyperbolicMeasure K)
      (Measure.pi (fun _ : InfinitePlace K => OAI.CubicEisenstein.hyperbolicEuclideanVolume)) :=
  measurePreserving_pi (fun _ : InfinitePlace K => sourceArchHyperbolicMeasure)
    (fun _ : InfinitePlace K => OAI.CubicEisenstein.hyperbolicEuclideanVolume)
    (fun _ => sourceArchUpperEuclideanMap_preserving)

omit [NumberField K] in
lemma sourceKPArchUpperEuclideanMap_left_inverse (p : SourceKPArchUpperHalfSpace K) :
    sourceKPArchEuclideanUpperMap K (sourceKPArchUpperEuclideanMap K p) = p := by
  funext v
  exact sourceArchUpperEuclideanMap_left_inverse (p v)

omit [NumberField K] in
lemma sourceKPArchUpperEuclideanMap_right_inverse
    (p : InfinitePlace K → OAI.CubicEisenstein.EuclideanSpatial)
    (hp : ∀ v, 0 < p v 2) :
    sourceKPArchUpperEuclideanMap K (sourceKPArchEuclideanUpperMap K p) = p := by
  funext v
  exact sourceArchUpperEuclideanMap_right_inverse (p v) (hp v)

local instance : MeasurableSpace (SourceKPArchSymmetricSpace K hζ) := borel _
local instance : BorelSpace (SourceKPArchSymmetricSpace K hζ) := ⟨rfl⟩

def sourceKPArchSymmetricHyperbolicMeasure : Measure (SourceKPArchSymmetricSpace K hζ) :=
  Measure.map (sourceKPArchSymmetricHomeomorph K hζ).symm (sourceKPArchHyperbolicMeasure K)

lemma sourceKPArchSymmetricHomeomorph_measurePreserving :
    MeasurePreserving (sourceKPArchSymmetricHomeomorph K hζ)
      (sourceKPArchSymmetricHyperbolicMeasure K hζ) (sourceKPArchHyperbolicMeasure K) :=
  MeasurePreserving.symm (sourceKPArchSymmetricHomeomorph K hζ).symm.toMeasurableEquiv
    ⟨(sourceKPArchSymmetricHomeomorph K hζ).symm.measurable, rfl⟩

def sourceKPArchEuclideanSymmetricMap
    (p : InfinitePlace K → OAI.CubicEisenstein.EuclideanSpatial) :
    SourceKPArchSymmetricSpace K hζ :=
  (sourceKPArchSymmetricHomeomorph K hζ).symm (sourceKPArchEuclideanUpperMap K p)

lemma sourceKPArchEuclideanSymmetricMap_preserving :
    MeasurePreserving (sourceKPArchEuclideanSymmetricMap K hζ)
      (Measure.pi (fun _ : InfinitePlace K => OAI.CubicEisenstein.hyperbolicEuclideanVolume))
      (sourceKPArchSymmetricHyperbolicMeasure K hζ) := by
  have hh : MeasurePreserving (sourceKPArchSymmetricHomeomorph K hζ).symm
      (sourceKPArchHyperbolicMeasure K) (sourceKPArchSymmetricHyperbolicMeasure K hζ) :=
    ⟨(sourceKPArchSymmetricHomeomorph K hζ).symm.measurable, rfl⟩
  exact hh.comp (sourceKPArchEuclideanUpperMap_preserving K)

instance sourceKPArchSymmetricHyperbolicMeasure_finiteOnCompacts :
    IsFiniteMeasureOnCompacts (sourceKPArchSymmetricHyperbolicMeasure K hζ) :=
  IsFiniteMeasureOnCompacts.map (sourceKPArchHyperbolicMeasure K)
    (sourceKPArchSymmetricHomeomorph K hζ).symm

instance sourceKPArchSymmetricHyperbolicMeasure_openPos :
    IsOpenPosMeasure (sourceKPArchSymmetricHyperbolicMeasure K hζ) :=
  (sourceKPArchSymmetricHomeomorph K hζ).symm.continuous.isOpenPosMeasure_map
    (sourceKPArchSymmetricHomeomorph K hζ).symm.surjective

instance sourceKPArchSymmetricHyperbolicMeasure_sigmaFinite :
    SigmaFinite (sourceKPArchSymmetricHyperbolicMeasure K hζ) :=
  (sourceKPArchSymmetricHomeomorph K hζ).symm.measurableEmbedding.sigmaFinite_map

lemma sourceKPArchSymmetricHyperbolicMeasure_preserving (a : PGL(2, InfiniteAdeleRing K)) :
    MeasurePreserving (fun p : SourceKPArchSymmetricSpace K hζ => a • p)
      (sourceKPArchSymmetricHyperbolicMeasure K hζ) (sourceKPArchSymmetricHyperbolicMeasure K hζ) := by
  refine ⟨(sourceKPArchSymmetric_action_continuous K hζ a).measurable, ?_⟩
  rw [sourceKPArchSymmetricHyperbolicMeasure, Measure.map_map
    (sourceKPArchSymmetric_action_continuous K hζ a).measurable
    (sourceKPArchSymmetricHomeomorph K hζ).symm.measurable]
  have he : (fun p : SourceKPArchSymmetricSpace K hζ => a • p) ∘
      (sourceKPArchSymmetricHomeomorph K hζ).symm =
      (sourceKPArchSymmetricHomeomorph K hζ).symm ∘ sourceKPArchUpperAction K hζ a := by
    funext p
    apply (sourceKPArchSymmetricHomeomorph K hζ).injective
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply, sourceKPArchSymmetricHomeomorph_smul]
  rw [he, ← Measure.map_map (sourceKPArchSymmetricHomeomorph K hζ).symm.measurable
    (sourceKPArchUpperAction_continuous K hζ a).measurable,
    (sourceKPArchUpperAction_preserving K hζ a).map_eq]

instance sourceKPArchSymmetricHyperbolicMeasure_smulInvariant :
    SMulInvariantMeasure (PGL(2, InfiniteAdeleRing K)) (SourceKPArchSymmetricSpace K hζ)
      (sourceKPArchSymmetricHyperbolicMeasure K hζ) where
  measure_preimage_smul a _s hs :=
    (sourceKPArchSymmetricHyperbolicMeasure_preserving K hζ a).measure_preimage hs.nullMeasurableSet

end
end ArtinMatthews
