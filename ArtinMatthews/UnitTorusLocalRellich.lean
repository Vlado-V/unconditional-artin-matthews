module

public import ArtinMatthews.UnitTorusRellich
public import Mathlib.MeasureTheory.Function.Holder


set_option backward.privateInPublic true
@[expose] public section

/-! Concrete cutoff and unit-cell versions of the normalized torus Rellich theorem. -/
namespace ArtinMatthews
open MeasureTheory UnitAddTorus Set
open scoped BigOperators Topology ENNReal
noncomputable section

variable (ι : Type*) [Fintype ι]

def unitTorusCutoffMultiplier (χ : C(UnitAddTorus ι, ℂ)) :
    UnitTorusL2 ι →L[ℂ] UnitTorusL2 ι :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL (unitTorusHaar ι) ∞ 2 2
    (χ.toLp ∞ (unitTorusHaar ι) ℂ)

theorem unitTorusCutoffMultiplier_coe (χ : C(UnitAddTorus ι, ℂ)) (f : UnitTorusL2 ι) :
    unitTorusCutoffMultiplier ι χ f =ᵐ[unitTorusHaar ι] fun x => χ x * f x := by
  have h := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder
    (r := 2) (χ.toLp ∞ (unitTorusHaar ι) ℂ) f
  filter_upwards [h, χ.coeFn_toLp (p := ∞) (𝕜 := ℂ) (unitTorusHaar ι)] with x hx hχ
  simpa only [unitTorusCutoffMultiplier, ContinuousLinearMap.holderL_apply_apply,
    ContinuousLinearMap.mul_apply', hχ] using hx

def unitTorusUnitCellMeasure : Measure (ι → ℝ) :=
  Measure.pi (fun _ : ι => (volume : Measure ℝ).restrict (Ioc 0 1))

def unitTorusUnitCellProjection (x : ι → ℝ) : UnitAddTorus ι :=
  fun j => (x j : UnitAddCircle)

theorem unitTorusUnitCellProjection_measurePreserving :
    MeasurePreserving (unitTorusUnitCellProjection ι) (unitTorusUnitCellMeasure ι)
      (unitTorusHaar ι) := by
  have hv : (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := by
    simpa only [ENNReal.ofReal_one, one_smul] using
      (AddCircle.volume_eq_smul_haarAddCircle (T := 1))
  have hc : MeasurePreserving (fun t : ℝ => (t : UnitAddCircle))
      ((volume : Measure ℝ).restrict (Ioc 0 1)) AddCircle.haarAddCircle := by
    simpa only [zero_add, hv] using UnitAddCircle.measurePreserving_mk 0
  exact measurePreserving_pi _ _ (fun _ : ι => hc)

def unitTorusUnitCellPullback : UnitTorusL2 ι →ₗᵢ[ℂ]
    Lp ℂ 2 (unitTorusUnitCellMeasure ι) :=
  Lp.compMeasurePreservingₗᵢ ℂ _ (unitTorusUnitCellProjection_measurePreserving ι)

theorem unitTorusUnitCellPullback_coe (f : UnitTorusL2 ι) :
    unitTorusUnitCellPullback ι f =ᵐ[unitTorusUnitCellMeasure ι]
      fun x => f (unitTorusUnitCellProjection ι x) :=
  Lp.coeFn_compMeasurePreserving f (unitTorusUnitCellProjection_measurePreserving ι)

def unitTorusUnitCellCutoff (χ : C(UnitAddTorus ι, ℂ)) :
    UnitTorusL2 ι →L[ℂ] Lp ℂ 2 (unitTorusUnitCellMeasure ι) :=
  (unitTorusUnitCellPullback ι).toContinuousLinearMap.comp (unitTorusCutoffMultiplier ι χ)

theorem unitTorusUnitCellCutoff_coe (χ : C(UnitAddTorus ι, ℂ)) (f : UnitTorusL2 ι) :
    unitTorusUnitCellCutoff ι χ f =ᵐ[unitTorusUnitCellMeasure ι]
      fun x => χ (unitTorusUnitCellProjection ι x) * f (unitTorusUnitCellProjection ι x) := by
  have h := (unitTorusUnitCellProjection_measurePreserving ι).quasiMeasurePreserving.ae
    (unitTorusCutoffMultiplier_coe ι χ f)
  filter_upwards [unitTorusUnitCellPullback_coe ι (unitTorusCutoffMultiplier ι χ f), h] with x hx hx'
  exact hx.trans hx'

variable [DecidableEq ι]

theorem unitTorusH1EnergySublevel_continuous_image_isCompact_closure
    {E : Type*} [TopologicalSpace E] [T2Space E] (F : UnitTorusL2 ι → E)
    (hF : Continuous F) (R : ℝ) :
    IsCompact (closure (F '' unitTorusH1EnergySublevel ι R)) := by
  have hK := (unitTorusH1EnergySublevel_isCompact_closure ι R).image hF
  apply hK.of_isClosed_subset isClosed_closure
  exact closure_minimal (Set.image_mono subset_closure) hK.isClosed

theorem unitTorusH1EnergySublevel_cutoff_isCompact_closure
    (χ : C(UnitAddTorus ι, ℂ)) (R : ℝ) :
    IsCompact (closure (unitTorusCutoffMultiplier ι χ '' unitTorusH1EnergySublevel ι R)) :=
  unitTorusH1EnergySublevel_continuous_image_isCompact_closure ι _
    (unitTorusCutoffMultiplier ι χ).continuous R

theorem unitTorusH1EnergySublevel_unitCell_isCompact_closure (R : ℝ) :
    IsCompact (closure (unitTorusUnitCellPullback ι '' unitTorusH1EnergySublevel ι R)) :=
  unitTorusH1EnergySublevel_continuous_image_isCompact_closure ι _
    (unitTorusUnitCellPullback ι).continuous R

theorem unitTorusH1EnergySublevel_unitCellCutoff_isCompact_closure
    (χ : C(UnitAddTorus ι, ℂ)) (R : ℝ) :
    IsCompact (closure (unitTorusUnitCellCutoff ι χ '' unitTorusH1EnergySublevel ι R)) :=
  unitTorusH1EnergySublevel_continuous_image_isCompact_closure ι _
    (unitTorusUnitCellCutoff ι χ).continuous R

end
end ArtinMatthews
