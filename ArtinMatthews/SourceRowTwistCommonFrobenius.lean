module

public import ArtinMatthews.SourceRowContinuedEuler
public import ArtinMatthews.KummerRowRayCharacters
public import ArtinMatthews.KummerPrimitiveRowInjectivity
public import ArtinMatthews.KummerRowFrobeniusTransfer
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

/-! Prime comparisons of the literal source twists in any common
sixth-Kummer field. Actual old and common modulus masks are retained. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators AngularLambda VaryingKummerAnalytic
open scoped NumberField Classical BigOperators nonZeroDivisors
noncomputable section
variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

def sourceRowCommonModulus (A : Finset F) : Ideal (𝓞 F) :=
  letI : Algebra F ℂ := sourceComplexAlgebra hζ
  rationalModulusIdeal (𝓞 F) (discriminantDegreeModulus F (sixthKummerRowField A))

omit [IsTotallyComplex F] in
theorem sourceRowCommonModulus_ne_bot (A : Finset F) :
    sourceRowCommonModulus F hζ A ≠ ⊥ := by
  let : Algebra F ℂ := sourceComplexAlgebra hζ
  exact rationalModulusIdeal_ne_bot _

variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable (u : sourceRing F S₀) (hu : u ≠ 0)
local notation "S" => sourceHilbertSet F S₀
local notation "v" => sourceRowFieldUnit F S₀ u hu
local notation "N" => sixthKummerSharpIdeal S v
local notation "hN" => sixthKummerSharpIdeal_ne_zero S v
local notation "χ" => sourceRowKummerRay F hζ S₀ u hu

theorem sourceRowKummerRay_common_prime (A : Finset F) (ha : ((v) : F) ∈ A)
    (P : ProbePrime F) (hP : IsCoprime P.asIdeal (sourceRowCommonModulus F hζ A)) :
    letI : Algebra F ℂ := sourceComplexAlgebra hζ
    (χ).idealHom (integralIdealFractionalUnit P.asIdeal P.ne_bot) =
      sixthKummerRowCharacter (sourcePrimitiveSix F hζ) A ((v) : F) ha (v).ne_zero
        (GaloisIdealCharacter.primeFrobenius F (sixthKummerRowField A) P) := by
  let : Algebra F ℂ := sourceComplexAlgebra hζ
  let R := discriminantDegreeModulus F (sixthKummerRowField A)
  let I : RayClass.primeToModulusIdeals (rationalIdealRayModulus F R) :=
    ⟨integralIdealFractionalUnit P.asIdeal P.ne_bot, integralPrime_mem_rationalPrimeTo R P hP⟩
  have h := sixthKummerRow_rayIdealHom_eq_individual (sourcePrimitiveSix F hζ)
    A ((v) : F) ha (v).ne_zero I
  have hG : GaloisIdealCharacter.idealHom F (sixthKummerRowField A)
        (sixthKummerRowCharacter (sourcePrimitiveSix F hζ) A ((v) : F) ha (v).ne_zero)
        (integralIdealFractionalUnit P.asIdeal P.ne_bot) =
      GaloisIdealCharacter.idealHom F (sixthKummerRowField {((v) : F)})
        (sixthKummerRowCharacter (sourcePrimitiveSix F hζ) {((v) : F)} ((v) : F)
          (Finset.mem_singleton_self _) (v).ne_zero)
        (integralIdealFractionalUnit P.asIdeal P.ne_bot) := by
    simpa only [sixthKummerRowRayCharacter_idealHom] using h
  have hRay : (χ).idealHom =
      GaloisIdealCharacter.idealHom F (sixthKummerRowField {((v) : F)})
        (sixthKummerRowCharacter (sourcePrimitiveSix F hζ) {((v) : F)} ((v) : F)
          (Finset.mem_singleton_self _) (v).ne_zero) :=
    sixthKummerSharpRayCharacter_idealHom (sourcePrimitiveSix F hζ) S (sourceWildPrimes_subset F S₀) v
  rw [hRay, ← hG, GaloisIdealCharacter.idealHom_prime]

variable {M : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F M) (hM : M ≠ ⊥)
local notation "ω" => sourceRowKummerTwist F hζ S₀ u hu η hM

theorem sourceRowTwist_common_prime (A : Finset F) (ha : ((v) : F) ∈ A)
    (P : ProbePrime F) (hP : IsCoprime P.asIdeal (sourceRowCommonModulus F hζ A)) :
    letI : Algebra F ℂ := sourceComplexAlgebra hζ
    (ω).idealHom (integralIdealFractionalUnit P.asIdeal P.ne_bot) =
      η.idealHom (integralIdealFractionalUnit P.asIdeal P.ne_bot) *
      (sixthKummerRowCharacter (sourcePrimitiveSix F hζ) A ((v) : F) ha (v).ne_zero
        (GaloisIdealCharacter.primeFrobenius F (sixthKummerRowField A) P))⁻¹ := by
  let : Algebra F ℂ := sourceComplexAlgebra hζ
  rw [sourceRowKummerTwist, EvenIdealRayCharacter.twistInverseAtProduct_idealHom,
    sourceRowKummerRay_common_prime F hζ S₀ u hu A ha P hP]

theorem sourceRowTwistPrimitive_common_prime (A : Finset F) (ha : ((v) : F) ∈ A)
    (P : ProbePrime F) (hold : IsCoprime P.asIdeal (M * N))
    (hP : IsCoprime P.asIdeal (sourceRowCommonModulus F hζ A)) :
    letI : Algebra F ℂ := sourceComplexAlgebra hζ
    (sourceRowTwistPrimitive F hζ S₀ u hu η hM).character.idealHom
      (integralIdealFractionalUnit P.asIdeal P.ne_bot) =
      η.idealHom (integralIdealFractionalUnit P.asIdeal P.ne_bot) *
      (sixthKummerRowCharacter (sourcePrimitiveSix F hζ) A ((v) : F) ha (v).ne_zero
        (GaloisIdealCharacter.primeFrobenius F (sixthKummerRowField A) P))⁻¹ := by
  let : Algebra F ℂ := sourceComplexAlgebra hζ
  let I := integralIdealPrimeToIdeal (M * N) (mul_ne_zero hM hN) P.asIdeal P.ne_bot hold
  exact ((sourceRowTwistPrimitive F hζ S₀ u hu η hM).agrees I).trans
    (sourceRowTwist_common_prime F hζ S₀ u hu η hM A ha P hP)

end
end ArtinMatthews.SourceEulerAssembly
