module

public import ArtinMatthews.SourceQuadraticEuler
public import ArtinMatthews.QuadraticHeckePrincipalNormPoisson


set_option backward.privateInPublic true
@[expose] public section

/-! The full norm Poisson formula for the actual zero-exponent source
character, with its principal residue and the genuine dual profile. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField Set MeasureTheory VaryingKummerAnalytic
open OAI.SevenEighths.ProbePhysical
open scoped NumberField ContDiff
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "Ideals" => {J : Ideal (𝓞 F) // J ≠ ⊥}

theorem sourceQuadraticRayCharacter_zero_allCoefficient
    (J : Ideal (𝓞 F)) (hJ : J ≠ ⊥) :
    (sourceQuadraticRayCharacter F S₀ hζ 0).allCoefficient J = 1 := by
  have hc : IsCoprime J (sourceQuadraticConductor F S₀ hζ 0) := by
    rw [sourceQuadraticConductor_zero]
    exact isCoprime_one_right
  rw [EvenIdealRayCharacter.allCoefficient, dite_eq_left hJ, ite_eq_left hc,
    sourceQuadraticRayCharacter_zero_idealHom, Units.val_one]

theorem sourceQuadraticRayCharacter_zero_normPoisson_dual_summable
    (w : ℝ → ℂ) (hc : HasCompactSupport w) (hp : tsupport w ⊆ Ioi 0)
    (hs : ContDiff ℝ ∞ w) {X : ℝ} (hX : 0 < X) :
    Summable (fun J : Ideals =>
      ‖(sourceQuadraticRayCharacter F S₀ hζ 0).allCoefficient J.val *
        quadraticHeckeDualProfile (quadraticHeckeFieldScale F)
          (InfinitePlace.nrComplexPlaces F) w (X * (Ideal.absNorm J.val : ℝ))‖) := by
  have hcoef (J : Ideals) :=
    sourceQuadraticRayCharacter_zero_allCoefficient F S₀ hζ J.val J.property
  simpa only [hcoef, one_mul] using
    quadraticHeckePrincipalNormPoisson_dual_summable F w hc hp hs hX

theorem sourceQuadraticRayCharacter_zero_normPoisson
    (w : ℝ → ℂ) (hc : HasCompactSupport w) (hp : tsupport w ⊆ Ioi 0)
    (hs : ContDiff ℝ ∞ w) {X : ℝ} (hX : 0 < X) :
    (∑' J : Ideals,
      (sourceQuadraticRayCharacter F S₀ hζ 0).allCoefficient J.val *
        w ((Ideal.absNorm J.val : ℝ) / X)) =
      (dedekindZeta_residue F : ℂ) * (X : ℂ) * mellin w 1 +
        (X : ℂ) * ∑' J : Ideals,
          (sourceQuadraticRayCharacter F S₀ hζ 0).allCoefficient J.val *
            quadraticHeckeDualProfile (quadraticHeckeFieldScale F)
              (InfinitePlace.nrComplexPlaces F) w (X * (Ideal.absNorm J.val : ℝ)) := by
  have hcoef (J : Ideals) :=
    sourceQuadraticRayCharacter_zero_allCoefficient F S₀ hζ J.val J.property
  simpa only [hcoef, one_mul] using quadraticHeckePrincipalNormPoisson F w hc hp hs hX

end
end ArtinMatthews.SourceEulerAssembly
