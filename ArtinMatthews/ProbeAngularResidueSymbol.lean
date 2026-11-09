module

public import ArtinMatthews.ProbeHilbertSReciprocity
public import ArtinMatthews.EisensteinAngularCyclotomic


set_option backward.privateInPublic true
@[expose] public section

/-! Identify the constructed complex sextic residue character with the
canonical number-field power-residue symbol. The comparison is proved by
reduction on roots of unity, without a residue-symbol identification premise. -/
namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain KummerTheory GlobalClassFieldTheory.Reciprocity
open AlgebraicNumberTheory.PowerResidueSymbols ArtinMatthews.AngularLambda
open OAI OAI.ActualEisensteinCubic OAI.ConcreteTraceCRT
open scoped NumberField BigOperators Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

abbrev probeSix : ℕ+ := ⟨6, by decide⟩

theorem probePrimeNorm_coprime_six (P : HeightOneSpectrum (𝓞 K))
    (hP : (6 : 𝓞 K) ∉ P.asIdeal) : (Ideal.absNorm P.asIdeal).Coprime 6 := by
  let : Field ((𝓞 K) ⧸ P.asIdeal) := Ideal.Quotient.field _
  let : Fintype ((𝓞 K) ⧸ P.asIdeal) := Fintype.ofFinite _
  obtain ⟨m, hp, hc⟩ := FiniteField.card ((𝓞 K) ⧸ P.asIdeal) (ringChar ((𝓞 K) ⧸ P.asIdeal))
  have hn : ¬ ringChar ((𝓞 K) ⧸ P.asIdeal) ∣ 6 := by
    intro hd
    apply hP
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_ofNat]
    exact (CharP.cast_eq_zero_iff ((𝓞 K) ⧸ P.asIdeal) (ringChar ((𝓞 K) ⧸ P.asIdeal)) 6).mpr hd
  rw [← card_primeIdealResidueField K P, hc]
  exact (hp.coprime_iff_not_dvd.mpr hn).pow_left _

theorem probePrimeResidueSymbol_reduce (P : HeightOneSpectrum (𝓞 K)) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hN : (Ideal.absNorm P.asIdeal).Coprime (n : ℕ)) (a : 𝓞 K) (ha : a ∉ P.asIdeal) :
    Ideal.Quotient.mk P.asIdeal
        (((primeIdealPowerResidueSymbol K P n hmu hN a ha).1 : (𝓞 K)ˣ) : 𝓞 K) =
      Ideal.Quotient.mk P.asIdeal a ^ ((Ideal.absNorm P.asIdeal - 1) / (n : ℕ)) := by
  let : Field ((𝓞 K) ⧸ P.asIdeal) := Ideal.Quotient.field _
  let : Fintype ((𝓞 K) ⧸ P.asIdeal) := Fintype.ofFinite _
  have h := rootsOfUnityReductionEquiv_primeIdealPowerResidueSymbol K P n hmu hN a ha
  have hv := congrArg (fun z : rootsOfUnity (n : ℕ) ((𝓞 K) ⧸ P.asIdeal) =>
    ((z.1 : ((𝓞 K) ⧸ P.asIdeal)ˣ) : (𝓞 K) ⧸ P.asIdeal)) h
  change Ideal.Quotient.mk P.asIdeal
      (((primeIdealPowerResidueSymbol K P n hmu hN a ha).1 : (𝓞 K)ˣ) : 𝓞 K) =
    Ideal.Quotient.mk P.asIdeal a ^ ((Fintype.card ((𝓞 K) ⧸ P.asIdeal) - 1) / (n : ℕ)) at hv
  simpa only [card_primeIdealResidueField K P] using hv

def probeIntegralSixthRoot [Algebra BaseField K] (z : BaseIntegers) (hz : z ^ 6 = 1) :
    rootsOfUnity 6 (𝓞 K) := by
  let u : BaseIntegersˣ := ⟨z, z ^ 5, by simpa only [← pow_succ'] using hz,
    by simpa only [← pow_succ] using hz⟩
  refine ⟨Units.map (algebraMap BaseIntegers (𝓞 K)).toMonoidHom u, ?_⟩
  apply Units.ext
  change (algebraMap BaseIntegers (𝓞 K) z) ^ 6 = 1
  rw [← map_pow, hz, map_one]

omit [NumberField K] in
theorem probeIntegralSixthRoot_val [Algebra BaseField K] (z : BaseIntegers) (hz : z ^ 6 = 1) :
    (((probeIntegralSixthRoot K z hz).1 : (𝓞 K)ˣ) : 𝓞 K) = algebraMap BaseIntegers (𝓞 K) z := rfl

variable [Algebra BaseField K]

local instance (P : HeightOneSpectrum (𝓞 K)) : (angularPrimeBelow K P).IsMaximal :=
  Ideal.isMaximal_under_of_isIntegral_of_isMaximal P.asIdeal

local instance (P : HeightOneSpectrum (𝓞 K)) : P.asIdeal.LiesOver (angularPrimeBelow K P) :=
  Ideal.over_under P.asIdeal

def probeAngularIntegralCharacter (P : HeightOneSpectrum (𝓞 K)) (hsix : (6 : 𝓞 K) ∉ P.asIdeal) :
    MulChar ((𝓞 K) ⧸ P.asIdeal) BaseIntegers := by
  let : Field ((𝓞 K) ⧸ P.asIdeal) := Ideal.Quotient.field _
  let : Fintype ((𝓞 K) ⧸ P.asIdeal) := Fintype.ofFinite _
  exact sexticResidueNormLift (angularPrimeBelow K P)
    (angularPrimeBelow_good K P (prime_not_three_of_not_six K P hsix)) ((𝓞 K) ⧸ P.asIdeal)

theorem probeAngularIntegralCharacter_pow_six (P : HeightOneSpectrum (𝓞 K))
    (hsix : (6 : 𝓞 K) ∉ P.asIdeal) (u : ((𝓞 K) ⧸ P.asIdeal)ˣ) :
    probeAngularIntegralCharacter K P hsix u ^ 6 = 1 := by
  let : Field ((𝓞 K) ⧸ P.asIdeal) := Ideal.Quotient.field _
  let : Fintype ((𝓞 K) ⧸ P.asIdeal) := Fintype.ofFinite _
  have horder : orderOf (probeAngularIntegralCharacter K P hsix) = 6 := by
    unfold probeAngularIntegralCharacter sexticResidueNormLift
    rw [FiniteFieldCharacter.normLift_orderOf, sexticChar_order _ _ (angularPrimeBelow_char_ne_two K P hsix)]
  have hp := pow_orderOf_eq_one (probeAngularIntegralCharacter K P hsix)
  rw [horder] at hp
  have hv := congrArg (fun χ : MulChar ((𝓞 K) ⧸ P.asIdeal) BaseIntegers => χ u) hp
  simpa only [MulChar.pow_apply_coe, MulChar.one_apply_coe] using hv

theorem probeAngularIntegralCharacter_complex (P : HeightOneSpectrum (𝓞 K))
    (hsix : (6 : 𝓞 K) ∉ P.asIdeal) (x : (𝓞 K) ⧸ P.asIdeal) :
    globalAngularResidueCharacter K P hsix x = eisEmbedding (probeAngularIntegralCharacter K P hsix x) := rfl

theorem probeAngularIntegralCharacter_reduce (P : HeightOneSpectrum (𝓞 K))
    (hsix : (6 : 𝓞 K) ∉ P.asIdeal) (u : ((𝓞 K) ⧸ P.asIdeal)ˣ) :
    Ideal.Quotient.mk P.asIdeal (algebraMap BaseIntegers (𝓞 K) (probeAngularIntegralCharacter K P hsix u)) =
      (u : (𝓞 K) ⧸ P.asIdeal) ^ ((Ideal.absNorm P.asIdeal - 1) / 6) := by
  let : Field ((𝓞 K) ⧸ P.asIdeal) := Ideal.Quotient.field _
  let : Fintype ((𝓞 K) ⧸ P.asIdeal) := Fintype.ofFinite _
  rw [← Ideal.Quotient.algebraMap_mk_of_liesOver P.asIdeal (angularPrimeBelow K P)]
  have h := sexticResidueNormLift_reduce_unit (angularPrimeBelow K P)
    (angularPrimeBelow_good K P (prime_not_three_of_not_six K P hsix)) ((𝓞 K) ⧸ P.asIdeal)
    (angularPrimeBelow_char_ne_two K P hsix) u
  simpa only [probeAngularIntegralCharacter, ← Nat.card_eq_fintype_card,
    card_primeIdealResidueField K P, Nat.card_eq_fintype_card] using h

theorem probeAngularIntegralCharacter_eq_symbol (P : HeightOneSpectrum (𝓞 K))
    (hsix : (6 : 𝓞 K) ∉ P.asIdeal) (hmu : (primitiveRoots 6 K).Nonempty)
    (a : 𝓞 K) (ha : a ∉ P.asIdeal) :
    probeIntegralSixthRoot K
        (probeAngularIntegralCharacter K P hsix (primeIdealResidueUnit K P a ha))
        (probeAngularIntegralCharacter_pow_six K P hsix (primeIdealResidueUnit K P a ha)) =
      primeIdealPowerResidueSymbol K P probeSix hmu (probePrimeNorm_coprime_six K P hsix) a ha := by
  apply rootsOfUnityReduction_injective K P probeSix (probePrimeNorm_coprime_six K P hsix)
  apply Subtype.ext
  apply Units.ext
  change Ideal.Quotient.mk P.asIdeal
      (algebraMap BaseIntegers (𝓞 K)
        (probeAngularIntegralCharacter K P hsix (primeIdealResidueUnit K P a ha))) =
    Ideal.Quotient.mk P.asIdeal
      (((primeIdealPowerResidueSymbol K P probeSix hmu (probePrimeNorm_coprime_six K P hsix) a ha).1 : (𝓞 K)ˣ) : 𝓞 K)
  rw [probeAngularIntegralCharacter_reduce]
  exact (probePrimeResidueSymbol_reduce K P probeSix hmu (probePrimeNorm_coprime_six K P hsix) a ha).symm

end
end ArtinMatthews.VaryingKummerAnalytic
