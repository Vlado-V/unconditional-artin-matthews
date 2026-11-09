module

public import ArtinMatthews.SourceGeneratorGlobalWeil
public import ArtinMatthews.SourceAnalyticWeilHecke


set_option backward.privateInPublic true
@[expose] public section

/-! The exact analytic source Hecke character has the actual quadratic
Gauss factor as its value at every exterior prime with an allowed
generator. Equality of extended ideals is proved from the generator's
ideal equation; no prime-value or local/global phase premise is used. -/

namespace ArtinMatthews

open NumberField IsDedekindDomain FractionalIdeal
open AllowedGenerators SIntegerPrincipalization SIntegerQuotient SIntegerFourier
open QuadraticWeil AngularLambda VaryingKummerAnalytic
open scoped NumberField Classical nonZeroDivisors

noncomputable section

variable (F : Type) [Field F] [NumberField F]

local instance primeCharacterQuotientField (P : HeightOneSpectrum (𝓞 F)) :
    Field (𝓞 F ⧸ P.asIdeal) := Ideal.Quotient.field _
local instance primeCharacterQuotientFinite (P : HeightOneSpectrum (𝓞 F)) :
    Finite (𝓞 F ⧸ P.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient P.ne_bot
local instance primeCharacterQuotientFintype (P : HeightOneSpectrum (𝓞 F)) :
    Fintype (𝓞 F ⧸ P.asIdeal) := Fintype.ofFinite _

theorem sourcePrime_extension_eq_principal
    (S₀ : Finset (HeightOneSpectrum (𝓞 F))) (P : HeightOneSpectrum (𝓞 F))
    (a : sourceRing F S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 F) (sourceRing F S₀)) = Ideal.span {a}) :
    extendedIdealGroup F S₀ (integralIdealFractionalUnit P.asIdeal P.ne_bot) =
      toPrincipalIdeal (sourceRing F S₀) F
        (generatorFieldUnit (sourceHilbertSeed F S₀) P a ha) := by
  apply Units.ext
  simp only [extendedIdealGroup, Units.coe_map, integralIdealFractionalUnit, Units.val_mk0,
    coe_toPrincipalIdeal]
  change fractionalIdealExtension F S₀ (P.asIdeal : FractionalIdeal (𝓞 F)⁰ F) =
    spanSingleton (sourceRing F S₀)⁰ (a : F)
  rw [fractionalIdealExtension, extendedHom_coeIdeal_eq_map, ha, coeIdeal_span_singleton]
  rw [Subalgebra.algebraMap_apply]

variable [IsTotallyComplex F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)

theorem sourceAnalyticWeilHeckeCharacter_prime
    (P : HeightOneSpectrum (𝓞 F)) (hP : P ∉ sourceHilbertSet F S₀)
    (a : sourceRing F S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 F) (sourceRing F S₀)) = Ideal.span {a})
    (hallowed : generatorFieldUnit (sourceHilbertSeed F S₀) P a ha ∈ allowedSubgroup F hζ S₀)
    (hsix : (6 : 𝓞 F) ∉ P.asIdeal) :
    ((sourceAnalyticWeilHeckeCharacter F hζ S₀ hS).idealHom
        (integralIdealFractionalUnit P.asIdeal P.ne_bot) : ℂ) =
      probeGaussGamma (cyclotomicAngularResidueCharacter hζ P hsix)
        (residueSourcePhase (sourceHilbertSeed F S₀) P hP a ha) 3 := by
  let u := generatorFieldUnit (sourceHilbertSeed F S₀) P a ha
  have hi : extendedIdealGroup F S₀ (integralIdealFractionalUnit P.asIdeal P.ne_bot) =
      extendedIdealGroup F S₀ (toPrincipalIdeal (𝓞 F) F u) :=
    (sourcePrime_extension_eq_principal F S₀ P a ha).trans
      (extendedIdealGroup_principal F S₀ u).symm
  have hv : (sourceAnalyticWeilHeckeCharacter F hζ S₀ hS).idealHom
      (integralIdealFractionalUnit P.asIdeal P.ne_bot) =
      (sourceAnalyticWeilHeckeCharacter F hζ S₀ hS).idealHom
        (toPrincipalIdeal (𝓞 F) F u) := by
    change sourceComplementIdealCharacter F hζ S₀ (sourceChosenWeilCharacter F hζ S₀ hS)
      (extendedIdealGroup F S₀ (integralIdealFractionalUnit P.asIdeal P.ne_bot)) =
        sourceComplementIdealCharacter F hζ S₀ (sourceChosenWeilCharacter F hζ S₀ hS)
          (extendedIdealGroup F S₀ (toPrincipalIdeal (𝓞 F) F u))
    exact congrArg _ hi
  have haV := sourceAnalyticWeilHeckeCharacter_allowed F hζ S₀ hS ⟨u, hallowed⟩
  exact (congrArg Units.val hv).trans (haV.trans
    (sourceGeneratorGammaThree_eq_SInverse F (sourceHilbertSeed F S₀) hS hζ P hP a ha hsix).symm)

include hS in
theorem sourceGammaThree_generator_independent
    (P : HeightOneSpectrum (𝓞 F)) (hP : P ∉ sourceHilbertSet F S₀)
    (a b : sourceRing F S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 F) (sourceRing F S₀)) = Ideal.span {a})
    (hb : P.asIdeal.map (algebraMap (𝓞 F) (sourceRing F S₀)) = Ideal.span {b})
    (haB : generatorFieldUnit (sourceHilbertSeed F S₀) P a ha ∈ allowedSubgroup F hζ S₀)
    (hbB : generatorFieldUnit (sourceHilbertSeed F S₀) P b hb ∈ allowedSubgroup F hζ S₀)
    (hsix : (6 : 𝓞 F) ∉ P.asIdeal) :
    probeGaussGamma (cyclotomicAngularResidueCharacter hζ P hsix)
        (residueSourcePhase (sourceHilbertSeed F S₀) P hP a ha) 3 =
      probeGaussGamma (cyclotomicAngularResidueCharacter hζ P hsix)
        (residueSourcePhase (sourceHilbertSeed F S₀) P hP b hb) 3 :=
  (sourceAnalyticWeilHeckeCharacter_prime F hζ S₀ hS P hP a ha haB hsix).symm.trans
    (sourceAnalyticWeilHeckeCharacter_prime F hζ S₀ hS P hP b hb hbB hsix)

end

end ArtinMatthews
