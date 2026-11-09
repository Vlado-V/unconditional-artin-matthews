module

public import ArtinMatthews.CyclotomicSourceWeil


set_option backward.privateInPublic true
@[expose] public section

/-! The cubic angular Gauss identity holds in the literal standard
generator phase. The additive phase is kept throughout the genuine
finite-field Jacobi calculation. -/

namespace ArtinMatthews.AngularLambda

open NumberField IsDedekindDomain
open SIntegerPrincipalization SIntegerQuotient SIntegerFourier
open VaryingKummerAnalytic
open OAI OAI.ActualEisensteinCubic OAI.ConcreteTraceCRT
open scoped NumberField Classical

noncomputable section

variable (F : Type) [Field F] [NumberField F] {ζ : F}

local instance sourceCubeQuotientField (P : HeightOneSpectrum (𝓞 F)) :
    Field (𝓞 F ⧸ P.asIdeal) := Ideal.Quotient.field _
local instance sourceCubeQuotientFinite (P : HeightOneSpectrum (𝓞 F)) :
    Finite (𝓞 F ⧸ P.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient P.ne_bot
local instance sourceCubeQuotientFintype (P : HeightOneSpectrum (𝓞 F)) :
    Fintype (𝓞 F ⧸ P.asIdeal) := Fintype.ofFinite _

theorem sourceAngularGammaTwo_cube (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
    (P : HeightOneSpectrum (𝓞 F)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 F) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (hbad : P ∉ StandardAdelic.traceBadPlaces F) (hsix : (6 : 𝓞 F) ∉ P.asIdeal) :
    probeGaussGamma (cyclotomicAngularResidueCharacter hζ P hsix)
        (residueSourcePhase S₀ P hP a ha) 2 ^ 3 =
      -cyclotomicAngularIdeal hζ P.asIdeal := by
  let : Algebra BaseField F := baseAlgebraOfTwelve hζ
  let : (angularPrimeBelow F P).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal P.asIdeal
  let : P.asIdeal.LiesOver (angularPrimeBelow F P) := Ideal.over_under P.asIdeal
  exact angularPrime_gammaTwo_cube F P.asIdeal (angularPrimeBelow F P)
    (angularPrimeBelow_good F P (prime_not_three_of_not_six F P hsix))
    (residueSourcePhase S₀ P hP a ha) (residueSourcePhase_primitive S₀ P hP a ha hbad)

end

end ArtinMatthews.AngularLambda
