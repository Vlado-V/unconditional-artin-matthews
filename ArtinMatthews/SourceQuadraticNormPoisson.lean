module

public import ArtinMatthews.SourceQuadraticEuler
public import ArtinMatthews.SourceQuadraticSelfDual
public import ArtinMatthews.QuadraticHeckeSelfDualContinuation
public import ArtinMatthews.QuadraticHeckePrimitivePoisson
public import ArtinMatthews.IdealRayCharacterProductCoefficients


set_option backward.privateInPublic true
@[expose] public section

/-! Exact norm Poisson for the paper's actual quadratic character family.
The functional-equation phase is derived from the genuine quadratic
Dedekind factorization; the conductor is its actual norm conductor. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField Set VaryingKummerAnalytic
open scoped NumberField Classical ContDiff
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceQuadraticRayCharacter_inverse_allCoefficient
    (e : SourcePrimeExponents F S₀) (J : Ideal (𝓞 F)) :
    (sourceQuadraticRayCharacter F S₀ hζ e).inverse.allCoefficient J =
      (sourceQuadraticRayCharacter F S₀ hζ e).allCoefficient J := by
  rw [EvenIdealRayCharacter.inverse_allCoefficient_conj]
  exact sourceQuadraticRayCharacter_star_allCoefficient F S₀ hζ e J

theorem sourceQuadraticRayCharacter_selfDual_continuation
    (e : SourcePrimeExponents F S₀) (he : ∀ P, e P ≤ 1) (hne : e ≠ 0) (s : ℂ) :
    (sourceQuadraticRayCharacter F S₀ hζ e).inverse.primitiveContinued
        (sourceQuadraticConductor_ne_bot F S₀ hζ e)
        ((sourceQuadraticRayCharacter F S₀ hζ e).inverse_isPrimitive
          (sourceQuadraticConductor_ne_bot F S₀ hζ e)
          (sourceQuadraticRayCharacter_primitive F S₀ hζ e)) s =
      (sourceQuadraticRayCharacter F S₀ hζ e).primitiveContinued
        (sourceQuadraticConductor_ne_bot F S₀ hζ e)
        (sourceQuadraticRayCharacter_primitive F S₀ hζ e) s := by
  exact (sourceQuadraticRayCharacter F S₀ hζ e).primitiveContinued_inverse_eq_of_real
    (sourceQuadraticRayCharacter_star_idealHom F S₀ hζ e)
    (sourceQuadraticConductor_ne_bot F S₀ hζ e)
    (sourceQuadraticRayCharacter_primitive F S₀ hζ e)
    (sourceQuadraticRayCharacter_isNonprincipal F S₀ hζ e he hne) s

theorem sourceQuadraticRayCharacter_normPoisson
    (e : SourcePrimeExponents F S₀) (he : ∀ P, e P ≤ 1) (hne : e ≠ 0)
    (w : ℝ → ℂ) (hc : HasCompactSupport w) (hp : tsupport w ⊆ Ioi 0)
    (hs : ContDiff ℝ ∞ w) {X : ℝ} (hX : 0 < X) :
    (∑' J : {J : Ideal (𝓞 F) // J ≠ ⊥},
      (sourceQuadraticRayCharacter F S₀ hζ e).allCoefficient J.val *
        w ((Ideal.absNorm J.val : ℝ) / X)) =
      (X / Real.sqrt (Ideal.absNorm (sourceQuadraticConductor F S₀ hζ e) : ℝ) : ℝ) *
        ∑' J : {J : Ideal (𝓞 F) // J ≠ ⊥},
          (sourceQuadraticRayCharacter F S₀ hζ e).allCoefficient J.val *
            quadraticHeckeDualProfile (quadraticHeckeFieldScale F)
              (InfinitePlace.nrComplexPlaces F) w
              ((Ideal.absNorm J.val : ℝ) * X /
                (Ideal.absNorm (sourceQuadraticConductor F S₀ hζ e) : ℝ)) := by
  have h := quadraticHeckePrimitiveNormPoisson_of_zeta_quotient F
    (SourceQuadraticField F S₀ hζ e) (sourceQuadraticRayCharacter F S₀ hζ e)
    (sourceQuadraticConductor_ne_bot F S₀ hζ e)
    (sourceQuadraticRayCharacter_primitive F S₀ hζ e)
    (sourceQuadraticRayCharacter_isNonprincipal F S₀ hζ e he hne)
    (sourceQuadraticRayCharacter_selfDual_continuation F S₀ hζ e he hne)
    (fun _ hs => sourceQuadraticRayCharacter_dedekind_factor F S₀ hζ e he hne hs)
    w hc hp hs hX
  simpa only [sourceQuadraticRayCharacter_inverse_allCoefficient F S₀ hζ e] using h

end
end ArtinMatthews.SourceEulerAssembly
