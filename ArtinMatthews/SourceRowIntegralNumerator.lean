module

public import ArtinMatthews.SourceAnalyticEulerParameters
public import ArtinMatthews.SixthKummerSharpRay


set_option backward.privateInPublic true
@[expose] public section

/-! The actual source S-integer has an integral numerator and a
denominator that is a unit at each exterior prime. This realizes
the exact sharp-ray mask from the derived source prime order. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators SIntegerPrincipalization SIntegerQuotient VaryingKummerAnalytic
open scoped NumberField Classical BigOperators nonZeroDivisors
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

local notation "R" => sourceRing F S₀
local notation "seed" => sourceHilbertSeed F S₀

def sourceRowFieldUnit (u : R) (hu : u ≠ 0) : Fˣ :=
  Units.mk0 (u : F) (fun h => hu (Subtype.ext h))

theorem sourceRowFieldUnit_val (u : R) (hu : u ≠ 0) : (sourceRowFieldUnit F S₀ u hu : F) = (u : F) :=
  rfl

theorem sourceRowIntegralNumerator (u : R) (hu : u ≠ 0) (P : SourceExteriorPrime F S₀) :
    ∃ a b : 𝓞 F, a ≠ 0 ∧ b ∉ P.val.asIdeal ∧ IsUnit (algebraMap (𝓞 F) R b) ∧
      u * algebraMap (𝓞 F) R b = algebraMap (𝓞 F) R a := by
  let d := principalizingDenominator seed
  let hd : d ≠ 0 := principalizingDenominator_ne_zero seed
  let : IsLocalization.Away d R := principalIntegerRing_isLocalization seed
  obtain ⟨m, a, h⟩ := exists_mul_pow_integer d hd (principalizingSet seed)
    (fun Q => mem_denominatorSupport _ _ Q) u
  let b := d ^ m
  have hdP : d ∉ P.val.asIdeal :=
    fun he => P.property ((mem_denominatorSupport d hd P.val).mpr he)
  have hbP : b ∉ P.val.asIdeal := fun he => hdP (P.val.isPrime.mem_of_pow_mem m he)
  have hb : IsUnit (algebraMap (𝓞 F) R b) := by
    dsimp only [b]
    rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit d).pow m
  have he : u * algebraMap (𝓞 F) R b = algebraMap (𝓞 F) R a := by
    apply Subtype.ext
    change (u : F) * algebraMap (𝓞 F) F b = algebraMap (𝓞 F) F a
    rw [show b = d ^ m from rfl, map_pow]
    exact h
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, map_zero] at he
    exact mul_ne_zero hu hb.ne_zero he
  exact ⟨a, b, ha0, hbP, hb, he⟩

theorem sourceRowIntegralNumerator_mem_iff (u : R) (P : SourceExteriorPrime F S₀) (a b : 𝓞 F)
    (hb : IsUnit (algebraMap (𝓞 F) R b))
    (he : u * algebraMap (𝓞 F) R b = algebraMap (𝓞 F) R a) :
    u ∈ P.val.asIdeal.map (algebraMap (𝓞 F) R) ↔ a ∈ P.val.asIdeal := by
  let d := principalizingDenominator seed
  let : IsLocalization.Away d R := principalIntegerRing_isLocalization seed
  have hc : IsCoprime P.val.asIdeal (Ideal.span {d}) := by
    simpa only [pow_one] using principalPrimePower_coprime seed P.val P.property 1
  rw [← Ideal.mul_unit_mem_iff_mem _ hb, he]
  change a ∈ (P.val.asIdeal.map (algebraMap (𝓞 F) R)).under (𝓞 F) ↔ a ∈ P.val.asIdeal
  rw [away_under_map_of_coprime d P.val.asIdeal hc]

theorem sourceIntegralFieldUnit_count_ne_zero (P : ProbePrime F) (a : 𝓞 F) (ha : a ≠ 0) :
    exteriorPrincipalValuation P (Units.mk0 (a : F) (by exact_mod_cast ha)) ≠ 0 ↔ a ∈ P.asIdeal := by
  rw [exteriorPrincipalValuation, coe_toPrincipalIdeal, Units.val_mk0,
    ← FractionalIdeal.coeIdeal_span_singleton]
  exact principal_count_ne_zero_iff_mem F a ha P

variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
include hζ

theorem sourceElementExponents_zero_iff_not_mem (u : R) (hu : u ≠ 0)
    (P : SourceExteriorPrime F S₀) :
    sourceElementExponents F S₀ u hu P = 0 ↔
      u ∉ P.val.asIdeal.map (algebraMap (𝓞 F) R) := by
  have h : u ∈ P.val.asIdeal.map (algebraMap (𝓞 F) R) ↔ 1 ≤ sourceElementExponents F S₀ u hu P := by
    simpa only [pow_one] using sourceElementExponents_mem_primePower_iff F S₀ hζ u hu P 1
  rw [h]
  omega

theorem sourceRowFieldUnit_count_zero_iff (u : R) (hu : u ≠ 0) (P : SourceExteriorPrime F S₀) :
    exteriorPrincipalValuation P.val (sourceRowFieldUnit F S₀ u hu) = 0 ↔
      sourceElementExponents F S₀ u hu P = 0 := by
  obtain ⟨a, b, ha0, hbP, hb, he⟩ := sourceRowIntegralNumerator F S₀ u hu P
  have hb0 : b ≠ 0 := fun h => hbP (h ▸ P.val.asIdeal.zero_mem)
  let aU := Units.mk0 (a : F) (by exact_mod_cast ha0)
  let bU := Units.mk0 (b : F) (by exact_mod_cast hb0)
  have heU : sourceRowFieldUnit F S₀ u hu * bU = aU := by
    apply Units.ext
    exact congrArg (fun v : R => (v : F)) he
  have hB : exteriorPrincipalValuation P.val bU = 0 := by
    by_contra h
    exact hbP ((sourceIntegralFieldUnit_count_ne_zero F P.val b hb0).mp h)
  have hVal := congrArg (exteriorPrincipalValuation P.val) heU
  rw [exteriorPrincipalValuation_mul, hB, add_zero] at hVal
  rw [hVal, sourceElementExponents_zero_iff_not_mem F S₀ hζ u hu P,
    sourceRowIntegralNumerator_mem_iff F S₀ u P a b hb he]
  simpa only [not_not] using not_congr (sourceIntegralFieldUnit_count_ne_zero F P.val a ha0)

end
end ArtinMatthews.SourceEulerAssembly
