module

public import ArtinMatthews.SourceReflectionPositiveTameFourier


set_option backward.privateInPublic true
@[expose] public section

/-! At a nonzero Fourier label the positive upper translation is the
same upper argument as in the actual tame Weyl rotation. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain VaryingKummerAnalytic
open scoped NumberField Classical

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "R" => (𝓞 K) ⧸ P.val.asIdeal
local notation "L" => P.val.adicCompletion K

attribute [local instance] positiveResidueField

theorem sourceReflectionPositiveLocalTranslation_unit (a : Rˣ) :
    sourceReflectionPositiveLocalTranslation K hζ S₀ P (a : R) =
      ((sourceKPTameExteriorUniformizer K hζ S₀ P ^ (-1 : ℤ) *
        sourceReflectionTameUnitLift K S₀ P a : Lˣ) : L) := by
  rw [sourceReflectionPositiveLocalTranslation, sourceReflectionPositiveResidueLift,
    dite_eq_right (Units.ne_zero a), Units.val_mul, Units.val_zpow_eq_zpow_val, zpow_neg_one]
  change (_ : L) * (sourceReflectionTameUnitLift K S₀ P (Units.mk0 (a:R) a.ne_zero) : L) =
    _ * (sourceReflectionTameUnitLift K S₀ P a : L)
  rw [show Units.mk0 (a:R) a.ne_zero = a from Units.ext rfl]

end
end ArtinMatthews
