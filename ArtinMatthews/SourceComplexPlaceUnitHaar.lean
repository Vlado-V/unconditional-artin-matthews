module

public import ArtinMatthews.SourceComplexUnitHaar
public import ArtinMatthews.SourceSLocalRadialSection


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion MeasureTheory
open ArtinMatthews.VaryingKummerAnalytic
open scoped NumberField ENNReal
noncomputable section

variable {K : Type} [Field K] {v : InfinitePlace K} (hv : IsComplex v)

def sourceComplexPlaceUnitsEquiv : v.Completionˣ ≃ₜ* ℂˣ :=
  Units.mapContinuousMulEquiv
    { toMulEquiv := (ringEquivComplexOfIsComplex hv).toMulEquiv
      continuous_toFun := (isometryEquivComplexOfIsComplex hv).continuous
      continuous_invFun := (isometryEquivComplexOfIsComplex hv).symm.continuous }

theorem sourceComplexPlaceUnitsEquiv_val (u : v.Completionˣ) :
    (sourceComplexPlaceUnitsEquiv hv u : ℂ) = ringEquivComplexOfIsComplex hv (u : v.Completion) := rfl

theorem sourceComplexPlaceUnitsEquiv_radial (t : ℝ) :
    sourceComplexPlaceUnitsEquiv hv (sourceComplexPlaceRadialUnit hv t) = sourceComplexRadialUnit t := by
  apply Units.ext
  rw [sourceComplexPlaceUnitsEquiv_val]
  change ringEquivComplexOfIsComplex hv ((ringEquivComplexOfIsComplex hv).symm (Real.exp (t / 2) : ℂ)) =
    (Real.exp (t / 2) : ℂ)
  exact (ringEquivComplexOfIsComplex hv).apply_symm_apply _

variable [MeasurableSpace v.Completion] [BorelSpace v.Completion]

theorem sourceComplexPlaceUnits_borel : BorelSpace v.Completionˣ := by
  constructor
  change (inferInstance : MeasurableSpace v.Completion).comap Units.val = borel v.Completionˣ
  rw [BorelSpace.measurable_eq (α := v.Completion), ← borel_comap]
  congr 1
  exact Units.isEmbedding_val₀.isInducing.eq_induced.symm

/-- The normalized complex-place Haar on the literal number field completion units. -/
def sourceComplexPlaceUnitHaar : Measure v.Completionˣ :=
  Measure.map (sourceComplexPlaceUnitsEquiv hv).symm sourceComplexUnitHaar

theorem sourceComplexPlaceUnitHaar_isHaar : (sourceComplexPlaceUnitHaar hv).IsHaarMeasure := by
  have : BorelSpace v.Completionˣ := sourceComplexPlaceUnits_borel (v := v)
  have : sourceComplexUnitHaar.IsHaarMeasure := sourceComplexUnitHaar_isHaar
  exact (sourceComplexPlaceUnitsEquiv hv).symm.isHaarMeasure_map sourceComplexUnitHaar

theorem sourceComplexPlaceUnitHaar_map_complex :
    Measure.map (fun u : v.Completionˣ => (sourceComplexPlaceUnitsEquiv hv u : ℂ))
      (sourceComplexPlaceUnitHaar hv) =
      sourceComplexTraceMeasure.withDensity (fun z : ℂ => ENNReal.ofReal ((‖z‖ ^ 2)⁻¹)) := by
  have : BorelSpace v.Completionˣ := sourceComplexPlaceUnits_borel (v := v)
  have h₁ : Measurable (fun u : v.Completionˣ => (sourceComplexPlaceUnitsEquiv hv u : ℂ)) :=
    Units.continuous_val.measurable.comp (sourceComplexPlaceUnitsEquiv hv).continuous.measurable
  have h₂ : Measurable ((sourceComplexPlaceUnitsEquiv hv).symm : ℂˣ → v.Completionˣ) :=
    (sourceComplexPlaceUnitsEquiv hv).symm.continuous.measurable
  rw [sourceComplexPlaceUnitHaar, Measure.map_map h₁ h₂]
  have he : (fun u : v.Completionˣ => (sourceComplexPlaceUnitsEquiv hv u : ℂ)) ∘
      (sourceComplexPlaceUnitsEquiv hv).symm = (Units.val : ℂˣ → ℂ) := by
    funext z
    simp only [Function.comp_apply, ContinuousMulEquiv.apply_symm_apply]
  rw [he, sourceComplexUnitHaar_map_val]

end
end ArtinMatthews.SourcePhysical
