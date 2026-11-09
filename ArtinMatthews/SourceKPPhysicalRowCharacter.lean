module

public import ArtinMatthews.SourceKPResidualWirtingerTheta
public import ArtinMatthews.SourceReflectionSUnitCharacterContinuous
public import ArtinMatthews.SourceReflectionWholeThetaCharacter


set_option backward.privateInPublic true
@[expose] public section

/-! The two exact multiplicative row weights used by the physical
Fourier expansion. Their difference is the oriented archimedean phase. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain QuadraticWeil VaryingKummerAnalytic SourceEulerAssembly AngularLambda SourcePhysical
open scoped NumberField Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12) (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S" => sourceHilbertSet K S₀
local notation "Whole" => SWholeUnits K S
variable {J : Ideal (𝓞 K)}

def sourceKPPhysicalRowFiniteCharacter (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
    (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥) (u : exteriorUnitSubgroup (sourceHilbertSet K S₀)) : Whole →* ℂˣ :=
  let theta := sourceReflectionLocalThetaCharacter K S₀ hJ hζ hS η
  let row := sourceReflectionSUnitCharacter K hζ S₀ u
  let proj : Whole →* SFiniteUnits K S := MonoidHom.snd _ _
  (theta.comp proj) * row

def sourceKPPhysicalRowWholeCharacter (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
    (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥) (u : exteriorUnitSubgroup (sourceHilbertSet K S₀)) : Whole →* ℂˣ :=
  (sourceReflectionWholeThetaCharacter K hζ S₀ hS η hJ) *
    (sourceReflectionSUnitCharacter K hζ S₀ u)

theorem sourceKPPhysicalRowFiniteCharacter_apply (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
    (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥) (u : exteriorUnitSubgroup (sourceHilbertSet K S₀)) (x : Whole) :
    sourceKPPhysicalRowFiniteCharacter K hζ S₀ hS η hJ u x =
      sourceReflectionLocalThetaCharacter K S₀ hJ hζ hS η x.2 *
        sourceReflectionSUnitCharacter K hζ S₀ u x := rfl

theorem sourceKPPhysicalRowWholeCharacter_apply (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
    (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥) (u : exteriorUnitSubgroup (sourceHilbertSet K S₀)) (x : Whole) :
    sourceKPPhysicalRowWholeCharacter K hζ S₀ hS η hJ u x =
      sourceReflectionWholeThetaCharacter K hζ S₀ hS η hJ x *
        sourceReflectionSUnitCharacter K hζ S₀ u x := rfl

theorem sourceKPPhysicalRowFiniteCharacter_continuous (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
    (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥) (u : exteriorUnitSubgroup (sourceHilbertSet K S₀)) :
    Continuous (sourceKPPhysicalRowFiniteCharacter K hζ S₀ hS η hJ u) := by
  change Continuous (fun x : Whole => sourceReflectionLocalThetaCharacter K S₀ hJ hζ hS η x.2 *
    sourceReflectionSUnitCharacter K hζ S₀ u x)
  exact ((sourceReflectionLocalThetaCharacter_continuous K S₀ hJ hζ hS η).comp
    continuous_snd).mul (sourceReflectionSUnitCharacter_continuous K hζ S₀ u)

theorem sourceKPPhysicalRowFiniteCharacter_norm (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
    (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥) (u : exteriorUnitSubgroup (sourceHilbertSet K S₀)) (x : Whole) :
    ‖(sourceKPPhysicalRowFiniteCharacter K hζ S₀ hS η hJ u x : ℂ)‖ = 1 := by
  rw [sourceKPPhysicalRowFiniteCharacter_apply,Units.val_mul,norm_mul,
    sourceReflectionLocalThetaCharacter_norm,sourceReflectionSUnitCharacter_norm,mul_one]

theorem sourceKPPhysicalRowWholeCharacter_diagonal (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
    (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥) (u : exteriorUnitSubgroup (sourceHilbertSet K S₀)) (m : Kˣ) :
    (sourceKPPhysicalRowWholeCharacter K hζ S₀ hS η hJ u (sWholeDiagonal K S m) : ℂ) =
      (sourceKPPhysicalRowFiniteCharacter K hζ S₀ hS η hJ u (sWholeDiagonal K S m) : ℂ) *
        sourceKPResidualArchAngular K (sourceKPOrientedHorizontal K hζ) m := by
  let d := sWholeDiagonal K S m
  have hA (v : InfinitePlace K) :
      complexAngular (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (IsTotallyComplex.isComplex v) (d.1 v : v.Completion)) ^
        (-sourceReflectionAngularInfinityExponent K hζ v) =
      complexAngular (v.embedding (m : K)) ^
        (if sourceKPOrientedHorizontal K hζ v then (-1 : ℤ) else 1) := by
    have he : NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (IsTotallyComplex.isComplex v) (d.1 v : v.Completion) = v.embedding (m : K) :=
      sourceKPCuspRationalComplexUnit_val K hζ m v
    rw [he]
    rcases sourceReflectionAngularInfinityExponent_sign K hζ v with hv | hv <;>
      simp [sourceKPOrientedHorizontal,hv]
  rw [sourceKPPhysicalRowWholeCharacter_apply,sourceKPPhysicalRowFiniteCharacter_apply,
    Units.val_mul,Units.val_mul,sourceReflectionWholeThetaCharacter_val]
  change _ = (_ : ℂ) * sourceKPResidualArchAngular K (sourceKPOrientedHorizontal K hζ) m
  simp only [sourceKPResidualArchAngular, ← hA]
  ring

end
end ArtinMatthews
