module

public import ArtinMatthews.ReflectionCoefficientRow
public import ArtinMatthews.SourceExponentFiniteFNorm
public import ArtinMatthews.SourceCoordinateSummability
public import ArtinMatthews.SourceExponentPowers


set_option backward.privateInPublic true
@[expose] public section

/-! The literal source05 four-ideal series. The global normalized gamma2
is kept as its genuine finite sum, with no multiplicativity replacement. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic QuadraticWeil
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable (hS : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
variable {M : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F M)

def sourceGlobalEulerTerm (u : sourceRing F S₀) (ξ w z : ℂ)
    (a : SourceExponentCoordinates F S₀) : ℂ :=
  reflectionGammaTwo F hζ S₀ a.1.val *
    reflectionThetaValue F hζ S₀ hS η (a.1.val + 3 • a.2.1) *
    sourceExponentFiniteF F hζ S₀ (reflectionPrimeCharacters F hζ S₀)
      a.2.2.1 (a.1.val + 3 • a.2.1)
      (u * sourcePrimeExponentGenerator F hζ S₀ a.2.2.2 ^ 6) *
    (sourcePrimeExponentNorm F S₀ a.1.val : ℂ) ^ (-(1 / 2 : ℂ) - ξ) *
    (sourcePrimeExponentNorm F S₀ a.2.1 : ℂ) ^ (-1 - 3 * ξ) *
    (sourcePrimeExponentNorm F S₀ a.2.2.1 : ℂ) ^ (-w) *
    (sourcePrimeExponentNorm F S₀ a.2.2.2 : ℂ) ^ (-(6 : ℂ) * z)

def sourceGlobalCalF (u : sourceRing F S₀) (ξ w z : ℂ) : ℂ :=
  ∑' a : SourceExponentCoordinates F S₀, sourceGlobalEulerTerm F hζ S₀ hS η u ξ w z a

end
end ArtinMatthews.SourceEulerAssembly
