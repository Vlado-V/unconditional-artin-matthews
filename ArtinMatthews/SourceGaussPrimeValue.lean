module

public import ArtinMatthews.SourceGaussCharacter
public import ArtinMatthews.EisensteinAngularCyclotomic
public import ArtinMatthews.SIntegerResidueGauss
public import ArtinMatthews.SIntegerStandardPhase
public import ArtinMatthews.AllowedIntegralGenerator
public import ArtinMatthews.SourceFourFrobenius
public import ArtinMatthews.SourceWeilPrimeCharacter
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

/-! The actual global finite-order Hecke character G has exactly the
source's normalized Gauss prime value, including the inverse chi(4)
factor. No Frobenius/residue, phase, or prime-value identity is assumed. -/

namespace ArtinMatthews

open NumberField IsDedekindDomain
open AllowedGenerators SIntegerPrincipalization SIntegerQuotient SIntegerFourier
open AngularLambda QuadraticWeil VaryingKummerAnalytic
open scoped NumberField Classical

noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)

local instance gaussPrimeQuotientField (P : HeightOneSpectrum (𝓞 F)) :
    Field (𝓞 F ⧸ P.asIdeal) := Ideal.Quotient.field _
local instance gaussPrimeQuotientFinite (P : HeightOneSpectrum (𝓞 F)) :
    Finite (𝓞 F ⧸ P.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient P.ne_bot
local instance gaussPrimeQuotientFintype (P : HeightOneSpectrum (𝓞 F)) :
    Fintype (𝓞 F ⧸ P.asIdeal) := Fintype.ofFinite _

theorem sourceGaussHeckeCharacter_prime_explicit
    (P : HeightOneSpectrum (𝓞 F)) (hP : P ∉ sourceHilbertSet F S₀)
    (a : sourceRing F S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 F) (sourceRing F S₀)) = Ideal.span {a})
    (hallowed : generatorFieldUnit (sourceHilbertSeed F S₀) P a ha ∈ allowedSubgroup F hζ S₀) :
    let hsix := source_exterior_six_not_mem F S₀ P hP
    ((sourceGaussHeckeCharacter F hζ S₀ hS).idealHom
        (integralIdealFractionalUnit P.asIdeal P.ne_bot) : ℂ) =
      (cyclotomicAngularResidueCharacter hζ P hsix (4 : 𝓞 F ⧸ P.asIdeal))⁻¹ *
        probeGaussGamma (cyclotomicAngularResidueCharacter hζ P hsix)
          (residueSourcePhase (sourceHilbertSeed F S₀) P hP a ha) 3 := by
  let : Algebra F ℂ := sourceComplexAlgebra hζ
  dsimp only
  rw [sourceGaussHeckeCharacter_idealHom, Units.val_mul, fourKummerInverseCorrection_prime,
    Units.val_inv_eq_inv_val,
    sourceFourFrobenius_value F hζ P (source_exterior_six_not_mem F S₀ P hP),
    sourceAnalyticWeilHeckeCharacter_prime F hζ S₀ hS P hP a ha hallowed]

theorem sourceGaussHeckeCharacter_prime
    (P : HeightOneSpectrum (𝓞 F)) (hP : P ∉ sourceHilbertSet F S₀)
    (a : sourceRing F S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 F) (sourceRing F S₀)) = Ideal.span {a})
    (hallowed : generatorFieldUnit (sourceHilbertSeed F S₀) P a ha ∈ allowedSubgroup F hζ S₀) :
    ((sourceGaussHeckeCharacter F hζ S₀ hS).idealHom
        (integralIdealFractionalUnit P.asIdeal P.ne_bot) : ℂ) =
      probeGaussLocalG (cyclotomicAngularResidueCharacter hζ P (source_exterior_six_not_mem F S₀ P hP))
        (residueSourcePhase (sourceHilbertSeed F S₀) P hP a ha) := by
  rw [probeGaussLocalG]
  exact sourceGaussHeckeCharacter_prime_explicit F hζ S₀ hS P hP a ha hallowed

theorem exists_sourceGaussHeckeCharacter_prime
    (P : HeightOneSpectrum (𝓞 F)) (hP : P ∉ sourceHilbertSet F S₀) :
    ∃ a : sourceRing F S₀,
      ∃ ha : P.asIdeal.map (algebraMap (𝓞 F) (sourceRing F S₀)) = Ideal.span {a},
        generatorFieldUnit (sourceHilbertSeed F S₀) P a ha ∈ allowedSubgroup F hζ S₀ ∧
        ((sourceGaussHeckeCharacter F hζ S₀ hS).idealHom
            (integralIdealFractionalUnit P.asIdeal P.ne_bot) : ℂ) =
          probeGaussLocalG
            (cyclotomicAngularResidueCharacter hζ P (source_exterior_six_not_mem F S₀ P hP))
            (residueSourcePhase (sourceHilbertSeed F S₀) P hP a ha) := by
  let I : exteriorIdeals (principalizingDenominator (sourceHilbertSeed F S₀)) :=
    ⟨P.asIdeal, P.ne_bot, by
      simpa only [pow_one] using principalPrimePower_coprime (sourceHilbertSeed F S₀) P hP 1⟩
  obtain ⟨a, ha0, ha, haB⟩ := exists_exterior_allowed_generator F hζ S₀ I
  have hallowed : generatorFieldUnit (sourceHilbertSeed F S₀) P a ha ∈
      allowedSubgroup F hζ S₀ := haB
  exact ⟨a, ha, hallowed, sourceGaussHeckeCharacter_prime F hζ S₀ hS P hP a ha hallowed⟩

end

end ArtinMatthews
