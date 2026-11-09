module

public import ArtinMatthews.IdealPrimeSexticWeil
public import ArtinMatthews.SIntegerResidueGauss
public import ArtinMatthews.StandardTameFiniteWeil


set_option backward.privateInPublic true
@[expose] public section

/-! The literal source generator phase agrees with the arbitrary-prime
analytic Gaussian character, including its minus sign and every unit
choice. The normalized cubic sextic Gauss factor is therefore the actual
local analytic Weil factor. -/

namespace ArtinMatthews.QuadraticWeil

open NumberField IsDedekindDomain ClassFieldTheory
open SIntegerPrincipalization SIntegerQuotient SIntegerFourier StandardAdelic
open VaryingKummerAnalytic OAI.SevenEighths OAI.SevenEighths.FiniteFourier
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
  (S₀ : Finset (HeightOneSpectrum (𝓞 F))) (P : HeightOneSpectrum (𝓞 F))

local instance sourceWeilMeasurable : MeasurableSpace (P.adicCompletion F) := borel (P.adicCompletion F)
local instance sourceWeilBorel : BorelSpace (P.adicCompletion F) := ⟨rfl⟩
local instance sourceWeilQuotientField : Field (𝓞 F ⧸ P.asIdeal) := Ideal.Quotient.field _
local instance sourceWeilQuotientFinite : Finite (𝓞 F ⧸ P.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient P.ne_bot
local instance sourceWeilQuotientFintype : Fintype (𝓞 F ⧸ P.asIdeal) := Fintype.ofFinite _

def sourceGeneratorCompletionUnit (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 F) (PrincipalIntegerRing S₀)) = Ideal.span {a}) :
    (P.adicCompletion F)ˣ :=
  Units.map (algebraMap F (P.adicCompletion F)).toMonoidHom (generatorFieldUnit S₀ P a ha)

theorem sourceGeneratorCompletionUnit_val (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 F) (PrincipalIntegerRing S₀)) = Ideal.span {a}) :
    (sourceGeneratorCompletionUnit F S₀ P a ha : P.adicCompletion F) =
      algebraMap F (P.adicCompletion F) (a : F) := rfl

theorem sourceGeneratorCompletionUnit_valuation (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 F) (PrincipalIntegerRing S₀)) = Ideal.span {a}) :
    (Valued.v : Valuation (P.adicCompletion F) (WithZero (Multiplicative ℤ)))
      (sourceGeneratorCompletionUnit F S₀ P a ha : P.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
  change Valued.v ((generatorFieldUnit S₀ P a ha : F) : P.adicCompletion F) = _
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact generatorFieldUnit_valuation S₀ P hP a ha

theorem residueSourcePhase_eq_negativeIdeal (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 F) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (hbad : P ∉ traceBadPlaces F) :
    residueSourcePhase S₀ P hP a ha =
      (idealPrimeResidueChar F P (localFiniteCharacter F P) (localFiniteCharacter_conductorZero F P hbad)
        (sourceGeneratorCompletionUnit F S₀ P a ha : P.adicCompletion F)
        (sourceGeneratorCompletionUnit_valuation F S₀ P hP a ha)).mulShift (-1) := by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [residueSourcePhase_mk, AddChar.mulShift_apply, neg_one_mul,
    ← map_neg (Ideal.Quotient.mk P.asIdeal) x, idealPrimeResidueChar_mk,
    sourceGeneratorCompletionUnit_val]
  congr 1
  rw [map_neg, map_div₀, ← IsScalarTower.algebraMap_apply (𝓞 F) F (P.adicCompletion F)]
  ring

theorem sourceGeneratorWeil_eq_sexticGamma {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 F) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (hbad : P ∉ traceBadPlaces F) (htwo : P ∉ GlobalClassFieldTheory.Reciprocity.powerResidueExponentFinitePlaces F 2)
    (χ : MulChar (𝓞 F ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6) :
    standardNormalizedWeil F (generatorFieldUnit S₀ P a ha)⁻¹ (.inr P) =
      probeGaussGamma χ (residueSourcePhase S₀ P hP a ha) 3 := by
  rw [standardNormalizedWeil_finite_eq_local, map_inv]
  change analyticNormalizedWeil (localFiniteCharacter F P)
    (sourceGeneratorCompletionUnit F S₀ P a ha)⁻¹ = _
  have h := adicPrimeUnit_normalizedWeil_eq_negativeSexticGamma_of_twelve F P hζ
    (localFiniteCharacter F P) (localFiniteCharacter_conductorZero F P hbad)
    (sourceGeneratorCompletionUnit F S₀ P a ha) (sourceGeneratorCompletionUnit_valuation F S₀ P hP a ha)
    (localFiniteCharacter_unitary F P) (localFiniteCharacter_continuous F P)
    (adic_two_eq_one_of_not_mem_exponent F P htwo) χ hχ
  rw [← residueSourcePhase_eq_negativeIdeal F S₀ P hP a ha hbad] at h
  exact h

theorem sourceGeneratorWeil_eq_tau {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 F) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (hbad : P ∉ traceBadPlaces F) (htwo : P ∉ GlobalClassFieldTheory.Reciprocity.powerResidueExponentFinitePlaces F 2)
    (χ : MulChar (𝓞 F ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6) :
    standardNormalizedWeil F (generatorFieldUnit S₀ P a ha)⁻¹ (.inr P) =
      residueSourceTau S₀ P hP a ha (χ ^ 3) / (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) := by
  rw [sourceGeneratorWeil_eq_sexticGamma F S₀ P hζ hP a ha hbad htwo χ hχ]
  have hcard : Fintype.card (𝓞 F ⧸ P.asIdeal) = Ideal.absNorm P.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  simp only [probeGaussGamma, ProbeGauss.normalizedGauss, gaussSum, residueSourceTau, tsum_fintype, hcard]

end

end ArtinMatthews.QuadraticWeil
