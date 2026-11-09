module

public import ArtinMatthews.SourceExteriorCRTFrame
public import ArtinMatthews.SourceFrequencyUnitReduction
public import ArtinMatthews.SourceDirectedRowPowers
public import ArtinMatthews.SourceLocalUnitFactorValue


set_option backward.privateInPublic true
@[expose] public section

/-! Exact directed rows of the actual finite-F unit multipliers. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic
open SIntegerPrincipalization SIntegerQuotient SourceCRTNormalization
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable (T : Finset (SourceExteriorPrime F S₀))

local notation "seed" => sourceHilbertSeed F S₀
local notation "R" => sourceRing F S₀
local notation "Pf" => sourceFramePrime F S₀ T
local notation "af" => sourceFrameGenerator F hζ S₀ T
local notation "χf" => sourceFrameCharacter F hζ S₀ T
local notation "hf" => sourceFramePrime_exterior F S₀ T
local notation "haf" => sourceFrameGenerator_ideal F hζ S₀ T

def sourceFrameFrequencyCofactor (u : R) (hu : u ≠ 0) (r : SourcePrimeExponents F S₀)
    (i : T) : PrincipalIntegerRing seed := sourceFrequencyCofactor F S₀ hζ u hu r i.val

theorem sourceFrameFrequencyCofactor_not_mem (u : R) (hu : u ≠ 0)
    (r : SourcePrimeExponents F S₀) (i : T) : sourceFrameFrequencyCofactor F hζ S₀ T u hu r i ∉
      (Pf i).asIdeal.map (algebraMap (𝓞 F) (PrincipalIntegerRing seed)) :=
  (sourceFrequencyCofactor_spec F S₀ hζ u hu r i.val).2

theorem sourceExponentCRTUnitFactor_value (s A r : SourcePrimeExponents F S₀)
    (u : R) (hu : u ≠ 0) (i : T) :
    sourceExponentCRTUnitFactor F S₀ hζ (reflectionPrimeCharacters F hζ S₀) s A r u hu T i =
      ((sourceResidualCharacterUnit F hζ S₀ u hu i.val ^ ((s i.val : ℤ) - A i.val) *
        sourceFrameCofactorCharacter F hζ S₀ T s i ^ A i.val *
        sourceFrameCofactorCharacter F hζ S₀ T A i ^ ((A i.val : ℤ) - s i.val) : ℂˣ) : ℂ) := by
  let hp := sourceFrameFrequencyCofactor F hζ S₀ T u hu r i
  have hhp := sourceFrameFrequencyCofactor_not_mem F hζ S₀ T u hu r i
  have hunit : sourceCharacterUnit seed (Pf i) (hf i) (af i) (haf i) (χf i) hp hhp =
      sourceResidualCharacterUnit F hζ S₀ u hu i.val :=
    sourceFrequencyCharacterUnit_eq F hζ S₀ u hu r i.val
  have hv := sourceLocalUnitFactor_value seed (Pf i) (hf i) (af i) (haf i) (χf i)
    (s i.val) (A i.val) (sourcePrimeCofactor seed af (fun j => s j.val) i)
    (sourcePrimeCofactor seed af (fun j => A j.val) i) hp
    (sourcePrimeCofactor_not_mem seed Pf (sourceFramePrime_pairwise F S₀ T) hf af haf (fun j => s j.val) i)
    (sourcePrimeCofactor_not_mem seed Pf (sourceFramePrime_pairwise F S₀ T) hf af haf (fun j => A j.val) i) hhp
  exact hv.trans (congrArg (fun z : ℂˣ => ((z ^ ((s i.val : ℤ) - A i.val) *
    sourceFrameCofactorCharacter F hζ S₀ T s i ^ A i.val *
    sourceFrameCofactorCharacter F hζ S₀ T A i ^ ((A i.val : ℤ) - s i.val) : ℂˣ) : ℂ)) hunit)

theorem sourceExponentCRTUnitFactor_row (s A r : SourcePrimeExponents F S₀)
    (u : R) (hu : u ≠ 0) (i : T) :
    sourceExponentCRTUnitFactor F S₀ hζ (reflectionPrimeCharacters F hζ S₀) s A r u hu T i =
      ((sourceResidualCharacterUnit F hζ S₀ u hu i.val ^ ((s i.val : ℤ) - A i.val) *
        ∏ Q ∈ T, sourcePrimeCrossDiagonalUnit F hζ S₀ i.val Q ^
          ((A i.val : ℤ) * s Q + ((A i.val : ℤ) - s i.val) * A Q) : ℂˣ) : ℂ) := by
  rw [sourceExponentCRTUnitFactor_value, sourceFrameCofactorCharacter_prod,
    sourceFrameCofactorCharacter_prod, mul_assoc]
  exact congrArg (fun z : ℂˣ =>
    ((sourceResidualCharacterUnit F hζ S₀ u hu i.val ^ ((s i.val : ℤ) - A i.val) * z : ℂˣ) : ℂ))
    (sourceDirectedRow_powers T (sourcePrimeCrossDiagonalUnit F hζ S₀ i.val) s A i.val)

end
end ArtinMatthews.SourceEulerAssembly
