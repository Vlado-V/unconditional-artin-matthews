module

public import ArtinMatthews.SIntegerArtinTameSymbol
public import ArtinMatthews.SIntegerNormalizedValue


set_option backward.privateInPublic true
@[expose] public section

/-! Actual global/local sextic tame comparison for an S-integer unit
and a prime generator. CFT's first slot is the Artin input and its
second slot is the radical; the normalized prime value is proved -1. -/
namespace ArtinMatthews.SIntegerTameSymbol

open NumberField IsDedekindDomain KummerTheory LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField LocalClassFieldTheory.Kummer
open GlobalClassFieldTheory.Reciprocity AlgebraicNumberTheory.PowerResidueSymbols
open ArtinMatthews.SIntegerPrincipalization ArtinMatthews.SIntegerQuotient
open ArtinMatthews.SIntegerAdicResidue ArtinMatthews.SIntegerResidueSymbol
open ArtinMatthews.SIntegerAllowedReciprocity ArtinMatthews.VaryingKummerAnalytic
open scoped NumberField Classical ValuativeRel
noncomputable section
variable (K : Type) [Field K] [NumberField K]

theorem sourceArtinUnit_toField (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (x : PrincipalIntegerRing S₀)
    (hx : x ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)))
    (g : Kˣ) (hg : (g : K) = (x : K)) :
    integerUnitsToFieldUnits (ChosenFinitePlaceBaseCompletion (K := K) P)
        (sourceArtinUnit K S₀ P hP x hx) = finitePlaceHilbert_completionUnit K P g := by
  apply Units.ext
  change ((sourceArtinUnit K S₀ P hP x hx :
    𝒪[ChosenFinitePlaceBaseCompletion (K := K) P]) : ChosenFinitePlaceBaseCompletion (K := K) P) = _
  rw [sourceArtinUnit_spec, artinIntegralOfSInteger_val]
  exact congrArg (algebraMap K (ChosenFinitePlaceBaseCompletion (K := K) P)) hg.symm

theorem not_mem_exponent_of_not_mem_six (P : HeightOneSpectrum (𝓞 K))
    (hsix : (6 : 𝓞 K) ∉ P.asIdeal) : P ∉ powerResidueExponentFinitePlaces K probeSix := by
  intro hm
  exact hsix (Ideal.dvd_span_singleton.mp ((mem_powerResidueExponentFinitePlaces_iff K probeSix P).mp hm))

theorem sourceGlobalHilbert_unit_generator
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (hsix : (6 : 𝓞 K) ∉ P.asIdeal) (hmu : (primitiveRoots 6 K).Nonempty)
    (x : PrincipalIntegerRing S₀)
    (hx : x ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)))
    (g : Kˣ) (hg : (g : K) = (x : K)) :
    finitePlaceHilbertSymbol K probeSix (by norm_num) hmu P g (generatorFieldUnit S₀ P a ha) =
      integralRootsOfUnityToNthRoots K 6
        (sIntegerPowerResidueSymbol K S₀ P hP a ha probeSix hmu
          (probePrimeNorm_coprime_six K P hsix) x hx) := by
  let C := ChosenFinitePlaceBaseCompletion (K := K) P
  let : ValuativeRel C := finitePlaceLocalArtinCompletionValuativeRel P
  let : IsNonarchimedeanLocalField C := finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField P
  let hPN := not_mem_exponent_of_not_mem_six K P hsix
  let hnC := finitePlace_natCast_valuation_eq_one_of_not_mem_exponent K probeSix P hPN
  let hmuC := finitePlaceHilbert_primitiveRoots_nonempty K probeSix hmu P
  apply nthRootsSubgroupMap_injective K C 6
  refine (finitePlaceHilbertSymbol_map_eq_localHilbertSymbol K probeSix (by norm_num)
    hmu P g (generatorFieldUnit S₀ P a ha)).trans ?_
  change LocalClassFieldTheory.Kummer.localHilbertSymbol C probeSix _ hmuC
    (finitePlaceHilbert_completionUnit K P g)
    (finitePlaceHilbert_completionUnit K P (generatorFieldUnit S₀ P a ha)) = _
  rw [← sourceArtinUnit_toField K S₀ P hP x hx g hg]
  rw [localHilbertSymbol_tame_formula C probeSix hnC hmuC]
  change localTamePowerResidueSymbol C probeSix hnC hmuC (sourceArtinUnit K S₀ P hP x hx) ^
    (-finitePlaceNormalizedValuation K P (generatorFieldUnit S₀ P a ha)) = _
  rw [normalizedValue_generator K S₀ P hP a ha, neg_neg, zpow_one]
  exact sourceArtin_tame_eq_symbol K S₀ P hP a ha probeSix hmu
    (probePrimeNorm_coprime_six K P hsix) hPN x hx

end
end ArtinMatthews.SIntegerTameSymbol
