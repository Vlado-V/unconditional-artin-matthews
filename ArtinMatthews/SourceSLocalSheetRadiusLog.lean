module

public import ArtinMatthews.SourceSLocalSheetCoordinates


set_option backward.privateInPublic true
@[expose] public section

/-! Logarithmic form of the forced positive radius on the actual sheet. -/

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace IsDedekindDomain
open scoped NumberField
noncomputable section

variable {K : Type} [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K))) (v : InfinitePlace K)

theorem sourceSheetRadius_eq_exp (y : SNormOneOtherUnits S v) :
    sourceSheetRadius S v y = Real.exp (-Real.log (sourceSheetOtherNorm S v y) / 2) := by
  rw [sourceSheetRadius, ← Real.exp_log (inv_pos.mpr (sourceSheetOtherNorm_pos S v y)),
    ← Real.exp_half, Real.log_inv]

theorem sourceSheetRadius_log_sq (y : SNormOneOtherUnits S v) :
    Real.log (sourceSheetRadius S v y ^ 2) = -Real.log (sourceSheetOtherNorm S v y) := by
  rw [sourceSheetRadius_sq, Real.log_inv]

variable {v}

theorem sourceSNormOneFromSheet_chosen_log_sq (hv : IsComplex v)
    (y : Circle × SNormOneOtherUnits S v) :
    Real.log (‖((sourceSNormOneFromSheet hv S y).val.1 v : v.Completion)‖ ^ 2) =
      -Real.log (sourceSheetOtherNorm S v y.2) := by
  rw [sourceSNormOneFromSheet_chosen_norm, sourceSheetRadius_log_sq]

end
end ArtinMatthews.SourcePhysical
