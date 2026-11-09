module

public import ArtinMatthews.SourceSLocalRadialHaar
public import ArtinMatthews.SourceComplexPlaceUnitHaar
public import ArtinMatthews.SourceSLocalSheetRadiusLog
public import ArtinMatthews.SourceSLocalWholeSplit
public import ArtinMatthews.SourceSheetWeightedPointwise


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion IsDedekindDomain
open scoped NumberField Classical
noncomputable section

variable {K : Type} [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable {v : InfinitePlace K} (hv : IsComplex v)

def sourceSLocalRadialSheet (a : Circle × SNormOneOtherUnits S v) (t : ℝ) : SWholeUnits K S :=
  sourceSLocalRadialMulEquiv hv S (sourceSNormOneFromSheet hv S a, Multiplicative.ofAdd t)

theorem sourceSLocalRadial_other (t : ℝ) :
    sourceSheetOther S v (sourceSLocalRadial hv S t) = 1 := by
  apply Prod.ext
  · funext w
    change Pi.mulSingle (M := fun w => w.Completionˣ) v (sourceComplexPlaceRadialUnit hv t) w.val = 1
    simp only [Pi.mulSingle_eq_of_ne w.property]
  · rfl

theorem sourceSLocalRadialSheet_other (a : Circle × SNormOneOtherUnits S v) (t : ℝ) :
    sourceSheetOther S v (sourceSLocalRadialSheet S hv a t) = a.2 := by
  change sourceSheetOther S v ((sourceSNormOneFromSheet hv S a : SWholeUnits K S) *
    sourceSLocalRadial hv S t) = a.2
  rw [sourceSheetOther_mul, sourceSLocalRadial_other S hv, mul_one]
  apply Prod.ext
  · funext w
    exact sourceSNormOneFromSheet_other hv S a w
  · exact sourceSNormOneFromSheet_finite hv S a

theorem sourceSLocalRadialSheet_chosen (a : Circle × SNormOneOtherUnits S v) (t : ℝ) :
    (sourceComplexPlaceUnitsEquiv hv ((sourceSLocalRadialSheet S hv a t).1 v) : ℂ) =
      sourceSheetComplexCoordinate (sourceSheetOtherNorm S v) t a.1 a.2 := by
  have hmul : (sourceSLocalRadialSheet S hv a t).1 v =
      (sourceSNormOneFromSheet hv S a).val.1 v * (sourceSLocalRadial hv S t).1 v := rfl
  have hrad : (sourceSLocalRadial hv S t).1 v = sourceComplexPlaceRadialUnit hv t := by
    unfold sourceSLocalRadial
    exact Pi.mulSingle_eq_same v _
  rw [hmul, hrad, map_mul, Units.val_mul, sourceComplexPlaceUnitsEquiv_radial,
    sourceComplexPlaceUnitsEquiv_val, sourceSNormOneFromSheet_chosen_image,
    sourceSheetRadius_eq_exp, sourceSheetComplexCoordinate]
  change (a.1 : ℂ) * (Real.exp (-Real.log (sourceSheetOtherNorm S v a.2) / 2) : ℂ) *
    (Real.exp (t / 2) : ℂ) = _
  rw [mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, mul_comm]
  have he : -Real.log (sourceSheetOtherNorm S v a.2) / 2 + t / 2 =
      (t - Real.log (sourceSheetOtherNorm S v a.2)) / 2 := by ring
  rw [he]

/-- The log-radius shear is the exact transition from local product polar coordinates
to the genuine norm-one sheet and total S-local logarithmic norm. -/
theorem sourceSLocalRadialSheet_shear (a : Circle × SNormOneOtherUnits S v) (t : ℝ) :
    sourceSLocalRadialSheet S hv a (t + Real.log (sourceSheetOtherNorm S v a.2)) =
      (sourceSWholeSheetSplit S v).symm
        ((sourceComplexPlaceUnitsEquiv hv).symm
          (sourceComplexUnitPolarMulEquiv (a.1, Multiplicative.ofAdd t)), a.2) := by
  apply (sourceSWholeSheetSplit S v).injective
  rw [ContinuousMulEquiv.apply_symm_apply, sourceSWholeSheetSplit_apply,
    sourceSLocalRadialSheet_other]
  apply Prod.ext
  · apply (sourceComplexPlaceUnitsEquiv hv).injective
    apply Units.ext
    rw [ContinuousMulEquiv.apply_symm_apply, sourceSLocalRadialSheet_chosen,
      sourceSheetComplexCoordinate, add_sub_cancel_right]
    rfl
  · rfl

end
end ArtinMatthews.SourcePhysical
