module

public import ArtinMatthews.SourceRowFrobeniusValue
public import ArtinMatthews.SourceRowKummerMask
public import ArtinMatthews.IdealRayCharacterProductCoefficients


set_option backward.privateInPublic true
@[expose] public section

/-! The extracted source row coefficient and its twist are actual
finite-order ideal ray characters, with exact exterior masks. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators AngularLambda VaryingKummerAnalytic
open scoped NumberField Classical BigOperators nonZeroDivisors
noncomputable section
variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable (u : sourceRing F S₀) (hu : u ≠ 0)

local notation "S" => sourceHilbertSet F S₀
local notation "v" => sourceRowFieldUnit F S₀ u hu
local notation "N" => sixthKummerSharpIdeal S v

def sourceRowKummerRay : EvenIdealRayCharacter F N :=
  letI : Algebra F ℂ := sourceComplexAlgebra hζ
  sixthKummerSharpRayCharacter (sourcePrimitiveSix F hζ) S (sourceWildPrimes_subset F S₀) v

theorem sourceRowKummerRay_prime (P : SourceExteriorPrime F S₀) :
    (sourceRowKummerRay F hζ S₀ u hu).allCoefficient P.val.asIdeal =
      sourcePrimeRowCharacter F hζ S₀ u hu P := by
  let : Algebra F ℂ := sourceComplexAlgebra hζ
  let := sixthKummerRowField_isAbelianGalois (sourcePrimitiveSix F hζ) ({(v : F)} : Finset F)
  by_cases hj : sourceElementExponents F S₀ u hu P = 0
  · have hc := (sourceRowKummerSharp_coprime_iff F hζ S₀ u hu P).mpr hj
    rw [EvenIdealRayCharacter.allCoefficient, dite_eq_left P.val.ne_bot, ite_eq_left hc,
      sourceRowKummerRay, sixthKummerSharpRayCharacter_idealHom, GaloisIdealCharacter.idealHom_prime]
    exact sourceRowFrobenius_value F hζ S₀ P u hu hj
  · have hc : ¬ IsCoprime P.val.asIdeal N := fun h =>
      hj ((sourceRowKummerSharp_coprime_iff F hζ S₀ u hu P).mp h)
    rw [EvenIdealRayCharacter.allCoefficient_eq_zero_of_not_coprime _ _ hc,
      sourcePrimeRowCharacter_of_degree_pos F hζ S₀ u hu P (Nat.pos_of_ne_zero hj)]

theorem sourceRowKummerRay_isNonprincipal
    (hp : ¬ ∃ a : F, a ^ 6 = (u : F)) :
    (sourceRowKummerRay F hζ S₀ u hu).IsNonprincipal := by
  let : Algebra F ℂ := sourceComplexAlgebra hζ
  exact sixthKummerSharpRayCharacter_isNonprincipal (sourcePrimitiveSix F hζ)
    S (sourceWildPrimes_subset F S₀) v hp

variable {M : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F M) (hM : M ≠ ⊥)

def sourceRowKummerTwist : EvenIdealRayCharacter F (M * N) :=
  η.twistInverseAtProduct (sourceRowKummerRay F hζ S₀ u hu) hM (sixthKummerSharpIdeal_ne_zero S v)

theorem sourceRowKummerTwist_prime (P : SourceExteriorPrime F S₀) :
    (sourceRowKummerTwist F hζ S₀ u hu η hM).allCoefficient P.val.asIdeal =
      sourcePrimeRowTwist F hζ S₀ u hu η P := by
  rw [sourceRowKummerTwist, EvenIdealRayCharacter.twistInverseAtProduct_allCoefficient,
    sourceRowKummerRay_prime]
  rfl

end
end ArtinMatthews.SourceEulerAssembly
