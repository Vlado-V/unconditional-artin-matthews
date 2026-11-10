module

public import ArtinMatthews.QuadraticKummer
public import ArtinMatthews.SourceReflectionExpansion
public import ArtinMatthews.KummerIntegralFrobeniusResidue
public import ArtinMatthews.SourceAngularIntegralResidue
public import ArtinMatthews.SourceQuadraticPrimeResidue
public import ArtinMatthews.SourceRowIntegralNumerator
public import ArtinMatthews.SourceSixthUnitResidue
public import Mathlib.Algebra.Lie.OfAssociative
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

/-! An actual exterior Frobenius value of the quadratic Kummer family.
Clearing the source S-integer denominator changes the cubed radicand by
a sixth power of a unit in the residue field. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic
open VaryingKummerAnalytic.GaloisIdealCharacter AngularLambda AlgebraicNumberTheory.PowerResidueSymbols
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "R" => sourceRing F S₀
local notation "E" => SourcePrimeExponents F S₀

include hζ
omit [NumberField F] in
theorem sourcePrimitiveRootSix : IsPrimitiveRoot (ζ ^ 2) 6 := by
  simpa using hζ.pow_of_dvd (p := 2) (by decide) (by decide)

theorem sourceQuadraticPrimeFrobenius_eq_symbol (e : E)
    (P : SourceExteriorPrime F S₀) (hP : e P = 0) :
    letI : Algebra F ℂ := sourceComplexAlgebra hζ
    let u := sourcePrimeExponentUnit F hζ S₀ e
    (quadraticKummerCharacter (sourcePrimitiveRootSix F hζ) u
      (primeFrobenius F (QuadraticKummerField u) P.val) : ℂ) =
      sourceReflectionQuadraticSymbol F S₀ hζ (Finsupp.single P 1) e := by
  let : Algebra F ℂ := sourceComplexAlgebra hζ
  let u := sourcePrimeExponentUnit F hζ S₀ e
  let L := QuadraticKummerField u
  let r := sourcePrimeExponentGenerator F hζ S₀ e
  let hr := sourcePrimeExponentGenerator_ne_zero F hζ S₀ e
  let P₀ := P.val.asIdeal
  let ρ := sourceQuadraticExteriorResidueMap F S₀ hζ P
  let χ := reflectionPrimeCharacters F hζ S₀ P
  obtain ⟨a, b, _, hbP, hbunit, hab⟩ := sourceRowIntegralNumerator F S₀ r hr P
  have haP : a ∉ P₀ := by
    rw [← sourceRowIntegralNumerator_mem_iff F S₀ r P a b hbunit hab,
      ← sourceElementExponents_zero_iff_not_mem F S₀ hζ r hr P,
      sourceElementExponents_of_generator F S₀ hζ e]
    exact hP
  have habF : (u : F) * algebraMap (𝓞 F) F b = algebraMap (𝓞 F) F a :=
    (sourcePrimeExponentUnit_val F hζ S₀ e).symm ▸ congrArg (fun x : R => (x : F)) hab
  have habL : algebraMap F L (u : F) * algebraMap (𝓞 F) L b = algebraMap (𝓞 F) L a := by
    simpa only [map_mul, ← IsScalarTower.algebraMap_apply (𝓞 F) F L] using
      congrArg (algebraMap F L) habF
  let α := quadraticKummerSixthRoot u
  let x : L := α * algebraMap (𝓞 F) L b
  have hx : x ^ 6 = algebraMap (𝓞 F) L ((a * b) ^ 3) := by
    change (α * algebraMap (𝓞 F) L b) ^ 6 = _
    rw [mul_pow, quadraticKummerSixthRoot_pow, map_pow, map_mul, ← habL]
    ring
  have ha : (a * b) ^ 3 ∉ P₀ := by
    intro h
    exact (P.val.isPrime.mul_mem_iff_mem_or_mem.mp (P.val.isPrime.mem_of_pow_mem 3 h)).elim haP hbP
  have h6 := source_exterior_six_not_mem F S₀ P.val P.property
  have hμ : (primitiveRoots 6 F).Nonempty :=
    ⟨ζ ^ 2, (mem_primitiveRoots (by decide)).mpr (sourcePrimitiveRootSix F hζ)⟩
  let σ := primeFrobenius F L P.val
  have hb₀ : b ≠ 0 := fun h => hbP (h ▸ P₀.zero_mem)
  have hratio : σ x / x = σ α / α := by
    change σ (α * algebraMap (𝓞 F) L b) / (α * algebraMap (𝓞 F) L b) = _
    rw [map_mul, IsScalarTower.algebraMap_apply (𝓞 F) F L, σ.commutes,
      mul_div_mul_right _ _ ((map_ne_zero _).mpr (RingOfIntegers.coe_ne_zero_iff.mpr hb₀))]
  have hcomp := frobenius_integral_radical_residue F 6 P.val h6 hμ
    (probePrimeNorm_coprime_six F P.val h6) ((a * b) ^ 3) ha x hx
  change σ x / x = _ at hcomp
  rw [hratio] at hcomp
  have hval := congrArg (fun z : L => (z : ℂ)) hcomp
  have hcomplex : (quadraticKummerCharacter (sourcePrimitiveRootSix F hζ) u σ : ℂ) =
      χ (Ideal.Quotient.mk P₀ ((a * b) ^ 3)) := by
    rw [quadraticKummerCharacter_apply]
    apply hval.trans
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F L]
    change sourceComplexEmbedding hζ _ = _
    exact sourceComplexEmbedding_integralResidue hζ P.val h6 hμ ((a * b) ^ 3) ha
  have habρ : ρ r * Ideal.Quotient.mk P₀ b = Ideal.Quotient.mk P₀ a := by
    have hbρ := sourceQuadraticExteriorResidueMap_integral F S₀ hζ P b
    have haρ := sourceQuadraticExteriorResidueMap_integral F S₀ hζ P a
    calc
      _ = ρ r * ρ (algebraMap (𝓞 F) R b) := congrArg (fun z => ρ r * z) hbρ.symm
      _ = ρ (r * algebraMap (𝓞 F) R b) := (map_mul ρ _ _).symm
      _ = ρ (algebraMap (𝓞 F) R a) := congrArg ρ hab
      _ = _ := haρ
  have hχb : χ (Ideal.Quotient.mk P₀ b) ^ 6 = 1 := by
    let : Field (𝓞 F ⧸ P₀) := Ideal.Quotient.field _
    have hu : IsUnit (Ideal.Quotient.mk P₀ b) :=
      isUnit_iff_ne_zero.mpr (mt Ideal.Quotient.eq_zero_iff_mem.mp hbP)
    rw [← MulChar.pow_apply' χ (by decide : (6 : ℕ) ≠ 0), show χ ^ 6 = 1 from
      reflectionPrimeCharacters_pow_six F S₀ hζ P, MulChar.one_apply hu]
  change (quadraticKummerCharacter (sourcePrimitiveRootSix F hζ) u σ : ℂ) = _
  have habχ : χ (Ideal.Quotient.mk P₀ a) = χ (ρ r) * χ (Ideal.Quotient.mk P₀ b) := by
    exact (congrArg χ habρ).symm.trans (map_mul χ _ _)
  have hreduce : χ (Ideal.Quotient.mk P₀ ((a * b) ^ 3)) = χ (ρ r) ^ 3 := by
    simp only [map_pow, map_mul]
    rw [habχ]
    calc
      _ = χ (ρ r) ^ 3 * χ (Ideal.Quotient.mk P₀ b) ^ 6 := by ring
      _ = _ := by rw [hχb, mul_one]
  exact hcomplex.trans (hreduce.trans (sourceReflectionQuadraticSymbol_single F S₀ hζ P e).symm)

end
end ArtinMatthews.SourceEulerAssembly
