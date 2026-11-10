module

public import ArtinMatthews.SourceRowIntegralNumerator
public import ArtinMatthews.SourceRowFrobenius
public import ArtinMatthews.SourceAnalyticEulerParameters
public import ArtinMatthews.SourceLocalPhaseComparison
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

/-! The actual angular value of a source S-integer at an exterior
unit prime is its arithmetic Kummer Frobenius value. The denominator
is removed only after a genuine sixth-power cancellation. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators AngularLambda VaryingKummerAnalytic
open SIntegerPrincipalization SIntegerQuotient SIntegerFourier
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
local notation "R" => sourceRing F S₀
local notation "seed" => sourceHilbertSeed F S₀
variable (P : SourceExteriorPrime F S₀)
local notation "κ" => ((𝓞 F) ⧸ P.val.asIdeal)
local notation "χ" => reflectionPrimeCharacters F hζ S₀ P
local notation "mk₀" => Ideal.Quotient.mk P.val.asIdeal

def sourceRowReduction : R →+* κ := by
  let a : PrincipalIntegerRing seed := sourceAllowedPrimeGenerator F hζ S₀ P
  let e := generatorResidueEquiv seed P.val P.property a (sourceAllowedPrimeGenerator_ideal F hζ S₀ P)
  exact e.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {a}))

theorem sourceRowReduction_integer (x : 𝓞 F) :
    sourceRowReduction F hζ S₀ P (algebraMap (𝓞 F) R x) = mk₀ x :=
  generatorResidueEquiv_mk seed P.val P.property (sourceAllowedPrimeGenerator F hζ S₀ P)
    (sourceAllowedPrimeGenerator_ideal F hζ S₀ P) x

theorem sourceRowCharacter_eq_reduction (u : R) (hu : u ≠ 0)
    (hj : sourceElementExponents F S₀ u hu P = 0) :
    sourcePrimeRowCharacter F hζ S₀ u hu P = χ (sourceRowReduction F hζ S₀ P u) :=
  sourcePrimeRowCharacter_eq_residue F hζ S₀ u hu P hj

theorem sourceRowFrobenius_value (u : R) (hu : u ≠ 0)
    (hj : sourceElementExponents F S₀ u hu P = 0) :
    letI : Algebra F ℂ := sourceComplexAlgebra hζ
    let v := sourceRowFieldUnit F S₀ u hu
    (sixthKummerRowCharacter (sourcePrimitiveSix F hζ)
      {((v : F))} (v : F) (Finset.mem_singleton_self _) v.ne_zero
      (GaloisIdealCharacter.primeFrobenius F (sixthKummerRowField {((v : F))}) P.val) : ℂ) =
      sourcePrimeRowCharacter F hζ S₀ u hu P := by
  let : Algebra F ℂ := sourceComplexAlgebra hζ
  let v := sourceRowFieldUnit F S₀ u hu
  obtain ⟨a, b, _, hbP, hb, hab⟩ := sourceRowIntegralNumerator F S₀ u hu P
  have hb0 : b ≠ 0 := fun h => hbP (h ▸ P.val.asIdeal.zero_mem)
  have huP := (sourceElementExponents_zero_iff_not_mem F S₀ hζ u hu P).mp hj
  have haP : a ∉ P.val.asIdeal := fun h =>
    huP ((sourceRowIntegralNumerator_mem_iff F S₀ u P a b hb hab).mpr h)
  let x := a * b ^ (5 : ℕ)
  have hxP : x ∉ P.val.asIdeal := by
    intro h
    rcases P.val.isPrime.mem_or_mem h with h₁ | h₂
    · exact haP h₁
    · exact hbP (P.val.isPrime.mem_of_pow_mem 5 h₂)
  have habF : (u : F) * algebraMap (𝓞 F) F b = algebraMap (𝓞 F) F a :=
    congrArg (fun z : R => (z : F)) hab
  have hxF : (v : F) * (b : F) ^ 6 = (x : F) := by
    change (u : F) * (algebraMap (𝓞 F) F b) ^ 6 = algebraMap (𝓞 F) F (a * b ^ 5)
    rw [map_mul, map_pow, show (6 : ℕ) = 5 + 1 by decide, pow_succ', ← mul_assoc, habF]
  let red := sourceRowReduction F hζ S₀ P
  have habRed := congrArg red hab
  rw [map_mul, sourceRowReduction_integer F hζ S₀ P b, sourceRowReduction_integer F hζ S₀ P a] at habRed
  have hRed : mk₀ x = red u * (mk₀ b) ^ 6 := by
    dsimp only [x]
    have hb6 : (mk₀ b) ^ (6 : ℕ) = (mk₀ b) * (mk₀ b) ^ (5 : ℕ) := pow_succ' _ 5
    rw [map_mul, map_pow, ← habRed, mul_assoc, hb6]
  have hbRed : mk₀ b ≠ 0 := fun h => hbP (Ideal.Quotient.eq_zero_iff_mem.mp h)
  let : Field κ := Ideal.Quotient.field _
  have hbPow : χ (mk₀ b) ^ 6 = 1 :=
    sourcePrimeCharacter_unit_pow_six F hζ S₀ P (Units.mk0 _ hbRed)
  have hFrob := sourceRowFrobenius_scaled F hζ P.val (source_exterior_six_not_mem F S₀ P.val P.property)
    v b x hb0 hxP hxF
  calc
    _ = χ (mk₀ x) := hFrob
    _ = χ (red u) := by rw [hRed, map_mul, map_pow, hbPow, mul_one]
    _ = _ := (sourceRowCharacter_eq_reduction F hζ S₀ P u hu hj).symm

end
end ArtinMatthews.SourceEulerAssembly
