module

public import ArtinMatthews.SourceKPTameHilbertPhase
public import ArtinMatthews.ProbeCyclotomicCrossCancellation
public import ArtinMatthews.ReflectionCoefficientRow
public import ArtinMatthews.SourceGeneratorWeil
public import ArtinMatthews.SIntegerNormalizedValue
public import ArtinMatthews.SIntegerTameGlobalComparison
public import ArtinMatthews.SLocalHilbertExponent
public import ArtinMatthews.SourceAngularResidueValue
public import ArtinMatthews.SourceJacquetActualShell
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceAdicHilbertComparison
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
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

/-! The oriented cubic torus phase on integral representatives of
the actual residue field. The generator's CFT normalized value is
minus one, which fixes the inverse complex embedding in the model. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain ClassFieldTheory GlobalClassFieldTheory.Reciprocity
open AlgebraicNumberTheory.PowerResidueSymbols
open AllowedGenerators SIntegerPrincipalization SIntegerQuotient QuadraticWeil
open SIntegerTameSymbol SIntegerAllowedReciprocity VaryingKummerAnalytic AngularLambda
open OAI OAI.ActualEisensteinCubic OAI.ConcreteTraceCRT
open scoped NumberField Classical ValuativeRel
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPComplexEmbedding_sextic_residue (P : HeightOneSpectrum (𝓞 K))
    (h6 : (6 : 𝓞 K) ∉ P.asIdeal) (x : 𝓞 K) (hx : x ∉ P.asIdeal) :
    sourceComplexEmbedding hζ
      ((((primeIdealPowerResidueSymbol K P probeSix (probeCyclotomicSexticRoots hζ)
        (probePrimeNorm_coprime_six K P h6) x hx).val : (𝓞 K)ˣ) : 𝓞 K) : K) =
      cyclotomicAngularResidueCharacter hζ P h6 (Ideal.Quotient.mk _ x) := by
  let : Algebra BaseField K := baseAlgebraOfTwelve hζ
  let u := primeIdealResidueUnit K P x hx
  have hr := probeAngularIntegralCharacter_eq_symbol K P h6 (probeCyclotomicSexticRoots hζ) x hx
  have hv := congrArg (fun z : rootsOfUnity 6 (𝓞 K) =>
    sourceComplexEmbedding hζ (((z.val : (𝓞 K)ˣ) : 𝓞 K) : K)) hr
  change sourceComplexEmbedding hζ
      ((algebraMap BaseIntegers (𝓞 K) (probeAngularIntegralCharacter K P h6 u) : 𝓞 K) : K) = _ at hv
  apply hv.symm.trans
  apply (sourceComplexEmbedding_baseInteger hζ _).trans
  exact (probeAngularIntegralCharacter_complex K P h6 (u : (𝓞 K) ⧸ P.asIdeal)).symm

omit [NumberField K] in
private theorem sourceKPEmbeddedInverseSquare (e : K →+* ℂ) (z : rootsOfUnity 3 K) :
    (e ((((z⁻¹ ^ (2 : ℕ)).val : Kˣ) : K)))⁻¹ = e ((z.val : Kˣ) : K) ^ 2 := by
  let m := (rootsOfUnity 3 K).subtype
  have hm : (z⁻¹ ^ (2 : ℕ)).val = (z.val⁻¹) ^ (2 : ℕ) :=
    (map_pow m z⁻¹ 2).trans (congrArg (· ^ (2 : ℕ)) (map_inv m z))
  rw [hm, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, map_pow, map_inv₀, inv_pow, inv_inv]

theorem sourceKPTameUniformizerCharacter_reverse_square (P : HeightOneSpectrum (𝓞 K))
    (π u : (P.adicCompletion K)ˣ) :
    ((sourceKPTameUniformizerCharacter K hζ P π u : ℂˣ) : ℂ) =
      sourceComplexEmbedding hζ ((((sourceKPRootsTransport K hζ P).symm
        (sourceFiniteKPHilbert K hζ P u π)).val : Kˣ) : K) ^ 2 := by
  rw [sourceKPTameUniformizerCharacter_apply, sourceFiniteKPHilbert_skew K hζ P π u,
    sourceKPCentralComplex_value]
  let E := sourceKPRootsTransport K hζ P
  let z := sourceFiniteKPHilbert K hζ P u π
  have hz : E.symm (z⁻¹ ^ (2 : ℕ)) = (E.symm z)⁻¹ ^ (2 : ℕ) := by rw [map_pow, map_inv]
  rw [hz]
  exact sourceKPEmbeddedInverseSquare K (sourceComplexEmbedding hζ) (E.symm z)

theorem sourceKPRationalKPHilbert_transport (P : HeightOneSpectrum (𝓞 K)) (a b : Kˣ) :
    (sourceKPRootsTransport K hζ P).symm (sourceFiniteKPHilbert K hζ P
      (Units.map (algebraMap K (P.adicCompletion K)).toMonoidHom a)
      (Units.map (algebraMap K (P.adicCompletion K)).toMonoidHom b)) =
      sourceRationalKPHilbert K hζ a b P := rfl

variable (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

def sourceKPTameExteriorUniformizer : (P.val.adicCompletion K)ˣ :=
  sourceGeneratorCompletionUnit K (sourceHilbertSeed K S₀) P.val
    (sourceAllowedPrimeGenerator K hζ S₀ P) (sourceAllowedPrimeGenerator_ideal K hζ S₀ P)

theorem sourceKPTameExteriorUniformizer_valuation :
    sourceKPFiniteVal K P.val (sourceKPTameExteriorUniformizer K hζ S₀ P : P.val.adicCompletion K) =
      WithZero.exp (-1 : ℤ) :=
  sourceGeneratorCompletionUnit_valuation K (sourceHilbertSeed K S₀) P.val P.property _ _

theorem sourceKPRationalKPHilbert_unit_generator_complex (x : 𝓞 K) (hx : x ∉ P.val.asIdeal) :
    sourceComplexEmbedding hζ
      (((sourceRationalKPHilbert K hζ (primeAvoidingIntegralFieldUnit K P.val x hx)
        (sourceAllowedPrimeUnit K hζ S₀ P) P.val).val : Kˣ) : K) =
      reflectionPrimeCharacters K hζ S₀ P (Ideal.Quotient.mk _ x) ^ 2 := by
  let v := P.val
  let a := primeAvoidingIntegralFieldUnit K v x hx
  let b := sourceAllowedPrimeUnit K hζ S₀ P
  let h3 := sLocalPrimitiveRoots K 3 (sourceHilbertRootThree_isPrimitive K hζ)
  let h6 := probeCyclotomicSexticRoots hζ
  have hsix := source_exterior_six_not_mem K S₀ v P.property
  have hb : finitePlaceNormalizedValuation K v b = -1 :=
    normalizedValue_generator K (sourceHilbertSeed K S₀) v P.property
      (sourceAllowedPrimeGenerator K hζ S₀ P) (sourceAllowedPrimeGenerator_ideal K hζ S₀ P)
  have hs := finitePlaceHilbertSymbol_eq_primeIdealPowerResidueFactor K probeSix (by norm_num)
    h6 v (not_mem_exponent_of_not_mem_six K v hsix) (probePrimeNorm_coprime_six K v hsix) x hx b
  rw [hb, neg_neg, zpow_one] at hs
  let e := sourceComplexEmbedding hζ
  have hvalue : e (((finitePlaceHilbertSymbol K probeSix (by norm_num) h6 v a b).val : Kˣ) : K) =
      reflectionPrimeCharacters K hζ S₀ P (Ideal.Quotient.mk _ x) := by
    change e (((finitePlaceHilbertSymbol K probeSix (by norm_num) h6 v
      (primeAvoidingIntegralFieldUnit K v x hx) b).val : Kˣ) : K) = _
    rw [hs]
    exact sourceKPComplexEmbedding_sextic_residue K hζ v hsix x hx
  have hcompare : sourceRationalKPHilbert K hζ a b v =
      globalFinitePlaceHilbertSymbol K 3 (by norm_num) h3 v a b :=
    finitePlaceAdicHilbertPairingFamily_finiteFactor K 3 (by norm_num) h3 v a b
  have hexp : (sourceRationalKPHilbert K hζ a b v).val =
      (finitePlaceHilbertSymbol K probeSix (by norm_num) h6 v a b).val ^ 2 := by
    rw [hcompare]
    exact globalFinitePlaceHilbertSymbol_exponent_compatibility K 3 probeSix h3 h6 (by decide) v a b
  let c : Kˣ := (finitePlaceHilbertSymbol K probeSix (by norm_num) h6 v a b).val
  have hE : (sourceRationalKPHilbert K hζ (primeAvoidingIntegralFieldUnit K P.val x hx)
      (sourceAllowedPrimeUnit K hζ S₀ P) P.val).val = c ^ (2 : ℕ) := hexp
  have hV : sourceComplexEmbedding hζ (c : K) =
      reflectionPrimeCharacters K hζ S₀ P (Ideal.Quotient.mk _ x) := hvalue
  rw [hE, Units.val_pow_eq_pow_val, map_pow (sourceComplexEmbedding hζ), hV]

private theorem sourceKPComplex_four_eq_neg_two (z : ℂ) (hz : z ^ 6 = 1) :
    (z ^ 2) ^ 2 = z ^ (-2 : ℤ) := by
  have hn : z ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide : 6 ≠ 0)] at hz
    exact zero_ne_one hz
  have hp : (z ^ 2) ^ 2 * z ^ 2 = 1 := by
    rw [← pow_mul, ← pow_add]
    exact hz
  calc
    _ = (z ^ 2) ^ 2 * (z ^ 2 * (z ^ 2)⁻¹) := by rw [mul_inv_cancel₀ (pow_ne_zero _ hn), mul_one]
    _ = (z ^ 2)⁻¹ := by rw [← mul_assoc, hp, one_mul]
    _ = _ := by
      change (z ^ 2)⁻¹ = z ^ (-(↑(2 : ℕ) : ℤ))
      rw [zpow_neg, zpow_natCast]

theorem sourceKPResidueValue_four_eq_inv_square (x : 𝓞 K) (hx : x ∉ P.val.asIdeal) :
    let z := reflectionPrimeCharacters K hζ S₀ P (Ideal.Quotient.mk _ x)
    (z ^ 2) ^ 2 = z ^ (-2 : ℤ) := by
  dsimp only
  apply sourceKPComplex_four_eq_neg_two
  let R := (𝓞 K) ⧸ P.val.asIdeal
  let χ := reflectionPrimeCharacters K hζ S₀ P
  let u := primeIdealResidueUnit K P.val x hx
  have hχ := pow_orderOf_eq_one χ
  have horder : orderOf χ = 6 := sourceJacquetActualCharacter_order K hζ S₀ P
  rw [horder] at hχ
  have hv := congrArg (fun f : MulChar R ℂ => f (u : R)) hχ
  have hu : (u : R) = Ideal.Quotient.mk P.val.asIdeal x := rfl
  have hpow : χ (u : R) ^ 6 = 1 := by
    simpa only [MulChar.pow_apply_coe, MulChar.one_apply_coe] using hv
  rw [hu] at hpow
  exact hpow

theorem sourceKPTameExteriorCharacter_integral (x : 𝓞 K) (hx : x ∉ P.val.asIdeal) :
    ((sourceKPTameUniformizerCharacter K hζ P.val (sourceKPTameExteriorUniformizer K hζ S₀ P)
      (Units.map (algebraMap K (P.val.adicCompletion K)).toMonoidHom
        (primeAvoidingIntegralFieldUnit K P.val x hx)) : ℂˣ) : ℂ) =
      reflectionPrimeCharacters K hζ S₀ P (Ideal.Quotient.mk _ x) ^ (-2 : ℤ) := by
  rw [sourceKPTameUniformizerCharacter_reverse_square]
  have hπ : sourceKPTameExteriorUniformizer K hζ S₀ P =
      Units.map (algebraMap K (P.val.adicCompletion K)).toMonoidHom
        (sourceAllowedPrimeUnit K hζ S₀ P) := rfl
  rw [hπ, sourceKPRationalKPHilbert_transport,
    sourceKPRationalKPHilbert_unit_generator_complex K hζ S₀ P x hx]
  exact sourceKPResidueValue_four_eq_inv_square K hζ S₀ P x hx

end
end ArtinMatthews
