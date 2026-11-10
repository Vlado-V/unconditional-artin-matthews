module

public import ArtinMatthews.SourceReflectionExpansion
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The prime column of the literal reflected quadratic kernel is the
cube of the actual source residue character on the S-integer generator. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators SIntegerPrincipalization SIntegerQuotient
open VaryingKummerAnalytic OAI.SevenEighths.FiniteFourier
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "T" => sourceHilbertSeed F S₀
local notation "OS" => PrincipalIntegerRing T
local notation "E" => SourcePrimeExponents F S₀
local notation "pgen" => sourceAllowedPrimeGenerator F hζ S₀
local notation "pgenIdeal" => sourceAllowedPrimeGenerator_ideal F hζ S₀

def sourceQuadraticExteriorResidueMap (P : SourceExteriorPrime F S₀) :
    OS →+* 𝓞 F ⧸ P.val.asIdeal :=
  (generatorResidueEquiv T P.val P.property (pgen P) (pgenIdeal P)).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {pgen P} : Ideal OS))

theorem sourceQuadraticExteriorResidueMap_integral (P : SourceExteriorPrime F S₀) (x : 𝓞 F) :
    sourceQuadraticExteriorResidueMap F S₀ hζ P (algebraMap (𝓞 F) OS x) =
      Ideal.Quotient.mk _ x :=
  generatorResidueEquiv_mk T P.val P.property (pgen P) (pgenIdeal P) x

theorem sourceQuadraticLocalWeight_positive (P : SourceExteriorPrime F S₀)
    (n : ℕ) (hn : 0 < n) (x : OS) :
    sourcePrimeExponentLocalWeight F hζ S₀ (reflectionPrimeCharacters F hζ S₀) P n x =
      reflectionPrimeCharacters F hζ S₀ P
        (sourceQuadraticExteriorResidueMap F S₀ hζ P x) ^ n := by
  let χ := reflectionPrimeCharacters F hζ S₀ P
  let b : OS := pgen P
  let I : Ideal OS := Ideal.span {b ^ n}
  have he := Ideal.quotEquivOfEq_mk (R := OS)
    (generator_power_ideal T P.val b (pgenIdeal P) n) x
  change generatorPowerWeight T P.val P.property b (pgenIdeal P) χ n
    ((Ideal.quotEquivOfEq (generator_power_ideal T P.val b (pgenIdeal P) n))
      (Ideal.Quotient.mk (primePowerIdeal T P.val n) x)) = _
  refine (congrArg (generatorPowerWeight T P.val P.property b (pgenIdeal P) χ n) he).trans ?_
  change generatorPowerWeight T P.val P.property b (pgenIdeal P) χ n (Ideal.Quotient.mk I x) = _
  change (if h : 0 < n then
    (generatorResidueCharacter T P.val P.property b (pgenIdeal P) χ ^ n)
      (generatorResidueReduction T b n h (Ideal.Quotient.mk I x)) else 1) = _
  let χ' := generatorResidueCharacter T P.val P.property b (pgenIdeal P) χ
  let z := generatorResidueReduction T b n hn (Ideal.Quotient.mk I x)
  calc
    _ = (χ' ^ n) z := dite_eq_left hn
    _ = χ' z ^ n := MulChar.pow_apply' χ' hn.ne' z
    _ = χ' (Ideal.Quotient.mk (Ideal.span {b} : Ideal OS) x) ^ n :=
      congrArg (fun y => χ' y ^ n) (generatorResidueReduction_mk T b n hn x)
    _ = _ := rfl

theorem sourceReflectionExponentResidueValue_single (P : SourceExteriorPrime F S₀) (x : OS) :
    reflectionExponentResidueValue F hζ S₀ (Finsupp.single P 1) x =
      reflectionPrimeCharacters F hζ S₀ P (sourceQuadraticExteriorResidueMap F S₀ hζ P x) := by
  let χ := reflectionPrimeCharacters F hζ S₀
  change (Finsupp.single P (1 : ℕ)).prod (fun Q n => sourcePrimeExponentLocalWeight F hζ S₀ χ Q n x) = _
  rw [Finsupp.prod_single_index (a := P) (b := 1)
    (h := fun Q n => sourcePrimeExponentLocalWeight F hζ S₀ χ Q n x)
    (sourcePrimeExponentLocalWeight_zero F hζ S₀ χ P x),
    sourceQuadraticLocalWeight_positive F S₀ hζ P 1 Nat.zero_lt_one x, pow_one]

theorem sourceReflectionQuadraticSymbol_single (P : SourceExteriorPrime F S₀) (e : E) :
    sourceReflectionQuadraticSymbol F S₀ hζ (Finsupp.single P 1) e =
      reflectionPrimeCharacters F hζ S₀ P
        (sourceQuadraticExteriorResidueMap F S₀ hζ P (sourcePrimeExponentGenerator F hζ S₀ e)) ^ 3 := by
  exact congrArg (fun z : ℂ => z ^ 3)
    (sourceReflectionExponentResidueValue_single F S₀ hζ P (sourcePrimeExponentGenerator F hζ S₀ e))

end
end ArtinMatthews.SourceEulerAssembly
