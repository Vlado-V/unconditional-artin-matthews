module

public import ArtinMatthews.QuotientSectionScaling
public import ArtinMatthews.SourceKPArchHaar
public import ArtinMatthews.SourceKPArchRadialMeasure
public import ArtinMatthews.SourceKPRadialHighFlow


set_option backward.privateInPublic true
@[expose] public section

/-! The literal full-frame radial map scales the actual archimedean Haar measure. -/
namespace ArtinMatthews
open NumberField Matrix Topology MeasureTheory
open scoped NumberField MatrixGroups AdeleRing ENNReal
noncomputable section
variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance : MeasurableSpace (SourceKPArchSymmetricSpace K hζ) := borel _
local instance : BorelSpace (SourceKPArchSymmetricSpace K hζ) := ⟨rfl⟩

def sourceKPArchSymmetricRadialHomeomorph (t : ℝ) :
    SourceKPArchSymmetricSpace K hζ ≃ₜ SourceKPArchSymmetricSpace K hζ :=
  (sourceKPArchSymmetricHomeomorph K hζ).trans
    ((sourceKPArchRadialPointHomeomorph K t).trans (sourceKPArchSymmetricHomeomorph K hζ).symm)

theorem sourceKPArchSymmetricRadial_mk (t : ℝ) (g : PGL(2, InfiniteAdeleRing K)) :
    sourceKPArchSymmetricRadialHomeomorph K hζ t (QuotientGroup.mk g) =
      QuotientGroup.mk (sourceKPArchRadialFlow K hζ t g) := by
  apply (sourceKPArchSymmetricHomeomorph K hζ).injective
  simp only [sourceKPArchSymmetricRadialHomeomorph, Homeomorph.trans_apply,
    Homeomorph.apply_symm_apply]
  change sourceKPArchRadialPoint K t (sourceKPArchGramCoordinates K hζ g) =
    sourceKPArchGramCoordinates K hζ (sourceKPArchRadialFlow K hζ t g)
  exact (sourceKPArchRadialFlow_coordinates K hζ t g).symm

theorem sourceKPArchSymmetricRadial_map_measure (t : ℝ) :
    Measure.map (sourceKPArchSymmetricRadialHomeomorph K hζ t)
      (sourceKPArchSymmetricHyperbolicMeasure K hζ) =
        ENNReal.ofReal (sourceKPRadialHeightScale K t) •
          sourceKPArchSymmetricHyperbolicMeasure K hζ := by
  rw [sourceKPArchSymmetricHyperbolicMeasure, Measure.map_map
    (sourceKPArchSymmetricRadialHomeomorph K hζ t).measurable
    (sourceKPArchSymmetricHomeomorph K hζ).symm.measurable]
  have he : (sourceKPArchSymmetricRadialHomeomorph K hζ t) ∘
      (sourceKPArchSymmetricHomeomorph K hζ).symm =
      (sourceKPArchSymmetricHomeomorph K hζ).symm ∘ sourceKPArchRadialPoint K t := by
    funext p
    simp only [sourceKPArchSymmetricRadialHomeomorph, Homeomorph.trans_apply,
      Homeomorph.apply_symm_apply, Function.comp_apply]
    rfl
  rw [he, ← Measure.map_map (sourceKPArchSymmetricHomeomorph K hζ).symm.measurable
    (sourceKPArchRadialPoint_continuous K t).measurable,
    sourceKPArchRadialPoint_map_hyperbolicMeasure,
    Measure.map_smul _ (sourceKPArchSymmetricHomeomorph K hζ).symm.measurable.aemeasurable]
  rfl

theorem sourceKPArchRadialFlow_continuous_fixed (t : ℝ) :
    Continuous (sourceKPArchRadialFlow K hζ t) := by
  have harg : Continuous (fun g : PGL(2, InfiniteAdeleRing K) => (t,g)) :=
    continuous_const.prodMk continuous_id
  have h := (sourceKPArchRadialFlow_continuous K hζ).comp harg
  simpa only [Function.comp_def] using h

def sourceKPArchRadialHomeomorph (t : ℝ) :
    PGL(2, InfiniteAdeleRing K) ≃ₜ PGL(2, InfiniteAdeleRing K) where
  toFun := sourceKPArchRadialFlow K hζ t
  invFun := sourceKPArchRadialFlow K hζ (-t)
  left_inv g := by rw [sourceKPArchRadialFlow_add, neg_add_cancel, sourceKPArchRadialFlow_zero]
  right_inv g := by rw [sourceKPArchRadialFlow_add, add_neg_cancel, sourceKPArchRadialFlow_zero]
  continuous_toFun := sourceKPArchRadialFlow_continuous_fixed K hζ t
  continuous_invFun := sourceKPArchRadialFlow_continuous_fixed K hζ (-t)

theorem sourceKPArchRadialFlow_map_haar (t : ℝ) :
    Measure.map (sourceKPArchRadialFlow K hζ t) (sourceKPArchHaar K hζ) =
      ENNReal.ofReal (sourceKPRadialHeightScale K t) • sourceKPArchHaar K hζ := by
  have hbase : MeasurePreserving (sourceKPArchSymmetricRadialHomeomorph K hζ t)
      (sourceKPArchSymmetricHyperbolicMeasure K hζ)
      (ENNReal.ofReal (sourceKPRadialHeightScale K t) •
        sourceKPArchSymmetricHyperbolicMeasure K hζ) :=
    ⟨(sourceKPArchSymmetricRadialHomeomorph K hζ t).measurable,
      sourceKPArchSymmetricRadial_map_measure K hζ t⟩
  have h := quotientSectionMeasure_equivariant_transport
    (sourceKPArchBaseCompactSubgroup K hζ) (sourceKPArchFrameSection K hζ)
    (sourceKPArchFrameSection_rightInverse K hζ) (sourceKPArchFrameSection_continuous K hζ)
    (sourceKPArchSymmetricHyperbolicMeasure K hζ)
    (ENNReal.ofReal (sourceKPRadialHeightScale K t) • sourceKPArchSymmetricHyperbolicMeasure K hζ)
    (sourceKPArchCompactHaar K hζ) (sourceKPArchRadialFlow K hζ t)
    (sourceKPArchRadialHomeomorph K hζ t).continuous
    (fun g k => sourceKPArchRadialFlow_compact K hζ t g k.val k.property)
    (sourceKPArchSymmetricRadialHomeomorph K hζ t) hbase
    (fun g => (sourceKPArchSymmetricRadial_mk K hζ t g).symm)
  rw [quotientSectionMeasure_smul _ _ (sourceKPArchFrameSection_continuous K hζ)] at h
  exact h.map_eq

theorem sourceKPArchRadialFlow_image_haar (t : ℝ)
    (A : Set (PGL(2, InfiniteAdeleRing K))) (hA : MeasurableSet A) :
    sourceKPArchHaar K hζ (sourceKPArchRadialFlow K hζ t '' A) =
      ENNReal.ofReal (sourceKPRadialHeightScale K (-t)) * sourceKPArchHaar K hζ A := by
  have h := congrArg (fun μ : Measure (PGL(2, InfiniteAdeleRing K)) => μ A)
    (sourceKPArchRadialFlow_map_haar K hζ (-t))
  rw [Measure.map_apply (sourceKPArchRadialFlow_continuous_fixed K hζ (-t)).measurable hA,
    Measure.smul_apply] at h
  have hp : sourceKPArchRadialFlow K hζ (-t) ⁻¹' A =
      sourceKPArchRadialFlow K hζ t '' A := by
    exact ((sourceKPArchRadialHomeomorph K hζ t).image_eq_preimage_symm A).symm
  simpa only [hp, smul_eq_mul] using h

end
end ArtinMatthews
