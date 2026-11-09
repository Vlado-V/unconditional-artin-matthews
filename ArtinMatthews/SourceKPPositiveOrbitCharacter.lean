module

public import ArtinMatthews.SourceKPPhysicalRowCharacter
public import ArtinMatthews.SourceReflectionThetaSUnit
public import ArtinMatthews.SourceReflectionSUnitPhase
public import ArtinMatthews.SourceKPAllowedForwardOrbit
public import ArtinMatthews.ReflectionCoefficientBeforeGaussian


set_option backward.privateInPublic true
@[expose] public section

/-! The actual phase on the forward orbit is unchanged by the distinct
S-unit sixth powers and matches the original theta and row factors. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain QuadraticWeil VaryingKummerAnalytic SourcePhysical SourceEulerAssembly
open scoped NumberField Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ 12) (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S" => sourceHilbertSet K S₀
local notation "Whole" => SWholeUnits K S
local notation "E" => SourcePrimeExponents K S₀
local notation "C" => ReflectionSquarefreeExponents K S₀
local notation "Γ" => sNormOneSixthSubgroup K S
local notation "D" => sWholeDiagonal K S
local notation "gen" => sourcePrimeExponentUnit K hζ S₀
local notation "freq" => sourceKPAllowedSquarefreeCubeFieldEquiv K hζ S₀
variable {J : Ideal (𝓞 K)}

theorem sourceKPPhysicalRowWholeCharacter_gamma (hS : standardWeilBadPlaces K ⊆ S)
    (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥) (hcut : principalAngularCutoff K J ⊆ S)
    (u : ↥(exteriorUnitSubgroup (sourceHilbertSet K S₀))) (γ : Γ) :
    sourceKPPhysicalRowWholeCharacter K hζ S₀ hS η hJ u (γ.val : Whole) = 1 := by
  obtain ⟨r,hr⟩ := γ.property
  have he := congrArg (fun z : SNormOne K S => (z : Whole)) hr
  rw [sNormOneSixthMap_val, map_pow] at he
  have hρ : sourceReflectionSUnitCharacter K hζ S₀ u (γ.val : Whole) = 1 := by
    rw [← he, sourceReflectionSUnitCharacter_sixth K hζ S₀ u]
  rw [sourceKPPhysicalRowWholeCharacter_apply, sourceReflectionWholeThetaCharacter_sixth K hζ S₀ hS η hJ hcut γ,
    hρ,mul_one]

theorem sourceKPPhysicalRowWholeCharacter_orbit (hS : standardWeilBadPlaces K ⊆ S)
    (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥) (hcut : principalAngularCutoff K J ⊆ S)
    (u : ↥(exteriorUnitSubgroup (sourceHilbertSet K S₀))) (c : C) (n : E) (γ : Γ) :
    (sourceKPPhysicalRowWholeCharacter K hζ S₀ hS η hJ u (D (freq ((c,n),γ)).val) : ℂ) =
      reflectionThetaValue K hζ S₀ hS η (c.val + 3 • n) *
        reflectionExponentResidueValue K hζ S₀ (c.val + 3 • n) (sourceExteriorUnitToSourceRing K S₀ u) := by
  rw [sourceKPAllowedSquarefreeCubeFieldEquiv_diagonal K hζ S₀ c n γ, map_mul,
    sourceKPPhysicalRowWholeCharacter_gamma K hζ S₀ hS η hJ hcut u γ, mul_one,
    sourceKPPhysicalRowWholeCharacter_apply,Units.val_mul,
    ← sourceReflectionThetaValue_eq_whole K hζ S₀ hS η hJ hcut,
    sourceReflectionSUnitCharacter_primeExponent K hζ S₀ u]

theorem sourceKPPositiveOrbitArithmetic_total (hS : standardWeilBadPlaces K ⊆ S)
    (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥) (hcut : principalAngularCutoff K J ⊆ S)
    (e : E) (u : ExteriorUnitSixthClasses S) (c : C) (n : E) (γ : Γ) :
    let m := (freq ((c,n),γ)).val
    let r := sourceExteriorUnitSixthRepresentative S u
    (sourceKPPhysicalRowWholeCharacter K hζ S₀ hS η hJ r (D m) : ℂ) *
      reflectionExponentResidueValue K hζ S₀ e (sourcePrimeExponentGenerator K hζ S₀ (c.val + 3 • n)) *
      sourceKPRetainedExteriorWhittaker K hζ S₀ hS m =
    reflectionCoefficientBeforeGaussian K hζ S₀ hS η c n (sourceReflectionCanonicalRow K S₀ hζ e u) := by
  dsimp only
  rw [sourceKPPhysicalRowWholeCharacter_orbit K hζ S₀ hS η hJ hcut,
    sourceKPAllowedSquarefreeCubeFieldEquiv_exteriorWhittaker K hζ S₀ hS c n γ,
    reflectionCoefficientBeforeGaussian,
    sourceReflectionCanonicalRow_residue_twist K hζ S₀ e (c.val + 3 • n) u,
    ← sourceReflectionExponentResidueValue_sUnit_eq_classPhase K hζ S₀
      (sourceExteriorUnitSixthRepresentative S u) (c.val + 3 • n)]
  ring

end
end ArtinMatthews
