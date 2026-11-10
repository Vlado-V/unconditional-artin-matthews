module

public import ArtinMatthews.SourceFrequencyUnitPart
public import ArtinMatthews.ReflectionCoefficientRow
public import ArtinMatthews.ProbeAngularResidueSymbol
public import ArtinMatthews.SIntegerAllowedHilbertPair
public import ArtinMatthews.SIntegerAngularResidueSymbol
public import ArtinMatthews.SIntegerNormalizedValue
public import ArtinMatthews.SIntegerTameGlobalComparison
public import ArtinMatthews.SourceAngularResidueValue
public import ArtinMatthews.SourcePrimeExponentValuation
public import ArtinMatthews.SourceUnitWeightValues
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.PNatToNat
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The exterior power-residue factor of an actual row unit is the
oriented complex value of the local sextic Hilbert factor. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain KummerTheory LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField LocalClassFieldTheory.Kummer
open GlobalClassFieldTheory.Reciprocity AlgebraicNumberTheory.PowerResidueSymbols
open AllowedGenerators SIntegerPrincipalization SIntegerQuotient SIntegerResidueSymbol
open SIntegerAllowedReciprocity SIntegerTameSymbol SIntegerAdicResidue
open SourceCRTNormalization VaryingKummerAnalytic AngularLambda
open OAI OAI.ActualEisensteinCubic OAI.ConcreteTraceCRT
open scoped NumberField Classical ValuativeRel
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S" => sourceHilbertSet K S₀
local notation "Q" => sourceHilbertSeed K S₀
local notation "D" => SourcePrimeExponents K S₀
local notation "X" => exteriorUnitSubgroup S

def sourceReflectionSixthRootValue : nthRootsSubgroup K 6 →* ℂ where
  toFun z := sourceComplexEmbedding hζ (z.val : K)
  map_one' := map_one _
  map_mul' z w := map_mul (sourceComplexEmbedding hζ) (z.val : K) (w.val : K)

def sourceReflectionSexticHilbert (P : HeightOneSpectrum (𝓞 K)) (u a : Kˣ) : nthRootsSubgroup K 6 :=
  finitePlaceHilbertSymbol K probeSix (by norm_num) (sourceSixRoots K hζ) P u a

local notation "H" => sourceReflectionSexticHilbert K hζ
local notation "E" => sourceReflectionSixthRootValue K hζ

private theorem rowUnit_avoids_exterior (u : X) (P : SourceExteriorPrime K S₀) :
    sourceExteriorUnitToSourceRing K S₀ u ∉
      P.val.asIdeal.map (algebraMap (𝓞 K) (sourceRing K S₀)) := by
  intro hu
  have hv := (sourceExteriorPrincipalValuation_eq_zero_iff K P.val u.val).mp
    (u.property P.val P.property)
  let x : PrincipalIntegerRing Q := sourceExteriorUnitToSourceRing K S₀ u
  have hu' : x ∈ P.val.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing Q)) := hu
  have h := (principalInteger_power_mem_iff_valuation Q P.val P.property 1 x).mp
    (by simpa only [pow_one] using hu')
  change P.val.valuation K ((sourceExteriorUnitToSourceRing K S₀ u : sourceRing K S₀) : K) ≤
    WithZero.exp (-(1 : ℤ)) at h
  rw [sourceExteriorUnitToSourceRing_val, hv, ← WithZero.exp_zero] at h
  have ht := WithZero.exp_le_exp.mp h
  norm_num at ht

private theorem exterior_hilbert_eq_power (u : X) (P : SourceExteriorPrime K S₀) (e : D) :
    let x := sourceExteriorUnitToSourceRing K S₀ u
    let a := sourceAllowedPrimeGenerator K hζ S₀ P
    let ha := sourceAllowedPrimeGenerator_ideal K hζ S₀ P
    let hx := rowUnit_avoids_exterior K S₀ u P
    let h₆ := source_exterior_six_not_mem K S₀ P.val P.property
    H P.val u.val (sourcePrimeExponentUnit K hζ S₀ e) =
      (integralRootsOfUnityToNthRoots K 6 (sIntegerPowerResidueSymbol K Q P.val P.property a ha
        probeSix (sourceSixRoots K hζ) (probePrimeNorm_coprime_six K P.val h₆) x hx)) ^ e P := by
  let C := ChosenFinitePlaceBaseCompletion (K := K) P.val
  let : ValuativeRel C := finitePlaceLocalArtinCompletionValuativeRel P.val
  let : IsNonarchimedeanLocalField C := finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField P.val
  let h₆ := source_exterior_six_not_mem K S₀ P.val P.property
  let hPN := not_mem_exponent_of_not_mem_six K P.val h₆
  let hnC := finitePlace_natCast_valuation_eq_one_of_not_mem_exponent K probeSix P.val hPN
  let hmu := sourceSixRoots K hζ
  let hmuC := finitePlaceHilbert_primitiveRoots_nonempty K probeSix hmu P.val
  let x := sourceExteriorUnitToSourceRing K S₀ u
  let a := sourceAllowedPrimeGenerator K hζ S₀ P
  let ha := sourceAllowedPrimeGenerator_ideal K hζ S₀ P
  let hx := rowUnit_avoids_exterior K S₀ u P
  let b := sourcePrimeExponentUnit K hζ S₀ e
  let Z := sIntegerPowerResidueSymbol K Q P.val P.property a ha probeSix hmu
    (probePrimeNorm_coprime_six K P.val h₆) x hx
  change H P.val u.val b = (integralRootsOfUnityToNthRoots K 6 Z) ^ e P
  apply nthRootsSubgroupMap_injective K C 6
  rw [map_pow]
  refine (finitePlaceHilbertSymbol_map_eq_localHilbertSymbol K probeSix (by norm_num)
    hmu P.val u.val b).trans ?_
  change localHilbertSymbol C probeSix _ hmuC
    (finitePlaceHilbert_completionUnit K P.val u.val) (finitePlaceHilbert_completionUnit K P.val b) = _
  rw [← sourceArtinUnit_toField K Q P.val P.property x hx u.val rfl,
    localHilbertSymbol_tame_formula C probeSix hnC hmuC]
  change localTamePowerResidueSymbol C probeSix hnC hmuC (sourceArtinUnit K Q P.val P.property x hx) ^
    (-finitePlaceNormalizedValuation K P.val b) = _
  have hb : finitePlaceNormalizedValuation K P.val b = -(e P : ℤ) := by
    rw [normalizedValue_eq_log K P.val, show (b:K) = (sourcePrimeExponentGenerator K hζ S₀ e : K)
      from sourcePrimeExponentUnit_val K hζ S₀ e, sourcePrimeExponentGenerator_valuation,
      WithZero.log_exp]
  rw [hb, neg_neg,zpow_natCast,sourceArtin_tame_eq_symbol K Q P.val P.property a ha probeSix hmu
    (probePrimeNorm_coprime_six K P.val h₆) hPN x hx]
  rfl

theorem sourceReflectionLocalSUnitWeight_eq_hilbert
    (u : X) (e : D) (P : SourceExteriorPrime K S₀) :
    sourcePrimeExponentLocalWeight K hζ S₀ (reflectionPrimeCharacters K hζ S₀) P (e P)
        (sourceExteriorUnitToSourceRing K S₀ u) =
      E (H P.val u.val (sourcePrimeExponentUnit K hζ S₀ e)) := by
  let : Algebra BaseField K := baseAlgebraOfTwelve hζ
  let x := sourceExteriorUnitToSourceRing K S₀ u
  let a := sourceAllowedPrimeGenerator K hζ S₀ P
  let ha := sourceAllowedPrimeGenerator_ideal K hζ S₀ P
  let hx := rowUnit_avoids_exterior K S₀ u P
  let h₆ := source_exterior_six_not_mem K S₀ P.val P.property
  let χ := reflectionPrimeCharacters K hζ S₀ P
  let v := sIntegerResidueUnit K Q P.val P.property a ha x hx
  let Z := sIntegerPowerResidueSymbol K Q P.val P.property a ha probeSix (sourceSixRoots K hζ)
    (probePrimeNorm_coprime_six K P.val h₆) x hx
  have hχ : E (integralRootsOfUnityToNthRoots K 6 Z) = χ (v : (𝓞 K) ⧸ P.val.asIdeal) := by
    rw [show Z = probeIntegralSixthRoot K (probeAngularIntegralCharacter K P.val h₆ v)
      (probeAngularIntegralCharacter_pow_six K P.val h₆ v) from
      (sIntegerAngularRoot_eq_symbol K Q P.val P.property a ha h₆ (sourceSixRoots K hζ) x hx).symm]
    change sourceComplexEmbedding hζ ((algebraMap BaseIntegers (𝓞 K)
        (probeAngularIntegralCharacter K P.val h₆ v) : 𝓞 K) : K) = _
    rw [sourceComplexEmbedding_baseInteger]
    exact (probeAngularIntegralCharacter_complex K P.val h₆ (v : (𝓞 K) ⧸ P.val.asIdeal)).symm
  have hW := sourcePowerWeight_unitValue Q P.val P.property a ha χ (e P) x hx
  change _ = (χ (v : (𝓞 K) ⧸ P.val.asIdeal)) ^ e P at hW
  rw [exterior_hilbert_eq_power K hζ S₀ u P e,map_pow]
  exact hW.trans (congrArg (fun c : ℂ => c ^ e P) hχ.symm)

end
end ArtinMatthews
