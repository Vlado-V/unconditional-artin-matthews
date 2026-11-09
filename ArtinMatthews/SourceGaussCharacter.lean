module

public import ArtinMatthews.SourceWeilPrimeCharacter
public import ArtinMatthews.SourceAngularEmbedding
public import ArtinMatthews.SUnitKummerCorrection


set_option backward.privateInPublic true
@[expose] public section

/-! The actual finite-order source Gauss correction is the product of
the quadratic analytic Weil Hecke character and the inverse Kummer
character of four, using the oriented complex embedding. -/

namespace ArtinMatthews

open NumberField IsDedekindDomain
open AllowedGenerators VaryingKummerAnalytic AngularLambda QuadraticWeil
open GlobalClassFieldTheory.GlobalClassFields
open scoped NumberField Classical

noncomputable section

variable (F : Type) [Field F] [NumberField F]

theorem source_sixthWild_subset (S₀ : Finset (HeightOneSpectrum (𝓞 F))) :
    sixthWildPrimes F ⊆ sourceHilbertSet F S₀ := by
  intro P hP
  apply normSupport_subset_sourceHilbertSet F S₀ 6 (Or.inr (Or.inr rfl))
  apply mem_sUnitKummerNormSupport_of_asIdeal_dvd_natCast 6 ∅
  exact Ideal.dvd_span_singleton.mpr ((mem_sixthWildPrimes P).mp hP)

theorem source_exterior_six_not_mem (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
    (P : HeightOneSpectrum (𝓞 F)) (hP : P ∉ sourceHilbertSet F S₀) :
    (6 : 𝓞 F) ∉ P.asIdeal := by
  intro h
  exact hP (source_sixthWild_subset F S₀ ((mem_sixthWildPrimes P).mpr h))

variable [IsTotallyComplex F] {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)

def sourceGaussHeckeCharacter : EvenIdealRayCharacter F
    (sixthKummerFixedIdeal (sourceHilbertSet F S₀) *
      sixthKummerFixedIdeal (sourceHilbertSet F S₀)) := by
  letI : Algebra F ℂ := sourceComplexAlgebra hζ
  exact (fourKummerInverseCorrection (ζ := ζ ^ 2) (by simpa using hζ.pow_of_dvd (p := 2) (by decide) (by decide))
    (sourceHilbertSet F S₀) (source_sixthWild_subset F S₀)).multiplyAtProduct
      (sourceAnalyticWeilHeckeCharacter F hζ S₀ hS)
      (sixthKummerFixedIdeal_ne_zero _) (sixthKummerFixedIdeal_ne_zero _)

theorem sourceGaussHeckeCharacter_idealHom (I : FractionalIdealGroup F) :
    letI : Algebra F ℂ := sourceComplexAlgebra hζ
    (sourceGaussHeckeCharacter F hζ S₀ hS).idealHom I =
      (fourKummerInverseCorrection (ζ := ζ ^ 2) (by simpa using hζ.pow_of_dvd (p := 2) (by decide) (by decide))
        (sourceHilbertSet F S₀) (source_sixthWild_subset F S₀)).idealHom I *
      (sourceAnalyticWeilHeckeCharacter F hζ S₀ hS).idealHom I := rfl

theorem sourceGaussHeckeCharacter_sixth (I : FractionalIdealGroup F) :
    (sourceGaussHeckeCharacter F hζ S₀ hS).idealHom I ^ 6 = 1 := by
  let : Algebra F ℂ := sourceComplexAlgebra hζ
  rw [sourceGaussHeckeCharacter_idealHom, mul_pow,
    fourKummerInverseCorrection, sunitKummerInverseCorrection_pow_six]
  have h := sourceAnalyticWeilHeckeCharacter_sq F hζ S₀ hS I
  rw [one_mul, show 6 = 2 * 3 by decide, pow_mul, h, one_pow]

end

end ArtinMatthews
