module

public import ArtinMatthews.SIntegerAngularResidueSymbol


set_option backward.privateInPublic true
@[expose] public section

/-! The canonical twelfth-root field structure supplies the angular
power-residue comparison, without an Eisenstein algebra as an input. -/
namespace ArtinMatthews.SIntegerResidueSymbol

open NumberField IsDedekindDomain KummerTheory
open ArtinMatthews.SIntegerPrincipalization ArtinMatthews.SIntegerQuotient
open ArtinMatthews.VaryingKummerAnalytic ArtinMatthews.AngularLambda
open OAI OAI.ActualEisensteinCubic OAI.ConcreteTraceCRT
open scoped NumberField Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K] {ζ : K}

omit [NumberField K] in
theorem cyclotomicSixRoots (hζ : IsPrimitiveRoot ζ 12) : (primitiveRoots 6 K).Nonempty := by
  refine ⟨ζ ^ 2, (mem_primitiveRoots (by decide : 0 < 6)).mpr ?_⟩
  exact hζ.pow_of_dvd (p := 2) (by decide) (by decide)

def cyclotomicSIntegerSixthRoot (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (hsix : (6 : 𝓞 K) ∉ P.asIdeal) (x : PrincipalIntegerRing S₀)
    (hx : x ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀))) : rootsOfUnity 6 (𝓞 K) := by
  letI := baseAlgebraOfTwelve hζ
  exact probeIntegralSixthRoot K
    (probeAngularIntegralCharacter K P hsix (sIntegerResidueUnit K S₀ P hP a ha x hx))
    (probeAngularIntegralCharacter_pow_six K P hsix (sIntegerResidueUnit K S₀ P hP a ha x hx))

theorem cyclotomicSIntegerSixthRoot_eq_symbol (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (hsix : (6 : 𝓞 K) ∉ P.asIdeal) (x : PrincipalIntegerRing S₀)
    (hx : x ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀))) :
    cyclotomicSIntegerSixthRoot K hζ S₀ P hP a ha hsix x hx =
      sIntegerPowerResidueSymbol K S₀ P hP a ha probeSix (cyclotomicSixRoots K hζ)
        (probePrimeNorm_coprime_six K P hsix) x hx := by
  let : Algebra BaseField K := baseAlgebraOfTwelve hζ
  exact sIntegerAngularRoot_eq_symbol K S₀ P hP a ha hsix (cyclotomicSixRoots K hζ) x hx

end
end ArtinMatthews.SIntegerResidueSymbol
