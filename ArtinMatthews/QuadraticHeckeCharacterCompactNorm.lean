module

public import ArtinMatthews.QuadraticHeckeCharacterCoprimeNorm
public import ArtinMatthews.QuadraticHeckeCompactNormSummability


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField Set MeasureTheory VaryingKummerAnalytic UniqueFactorizationMonoid
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]

/-- The compact character-weighted coprime norm sum has no summability premise. -/
theorem quadraticHeckeCharacterCoprimeNorm_reindex_compact {M : Ideal (𝓞 F)}
    (ψ : EvenIdealRayCharacter F M) (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (w : ℝ → ℂ) (hc : HasCompactSupport w) (hs : Continuous w)
    {X : ℝ} (hX : 0 < X) :
    (∑' J : {J : Ideal (𝓞 F) // J ≠ ⊥}, if IsCoprime J.val m then
      ψ.allCoefficient J.val * w ((Ideal.absNorm J.val : ℝ) / X) else 0) =
      ∑ d ∈ HeckeIdealMobius.divisors F m, (moebius d : ℂ) * ψ.allCoefficient d *
        ∑' J : {J : Ideal (𝓞 F) // J ≠ ⊥}, ψ.allCoefficient J.val *
          w ((Ideal.absNorm J.val : ℝ) / (X / (Ideal.absNorm d : ℝ))) :=
  quadraticHeckeCharacterCoprimeNorm_reindex F ψ m hm w hX
    (quadraticHeckeCompactNorm_summable F w hc hs hX)

end
end ArtinMatthews
