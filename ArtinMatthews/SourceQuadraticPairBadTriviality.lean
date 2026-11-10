module

public import ArtinMatthews.SourceQuadraticBlockIdeals
public import ArtinMatthews.SourceQuadraticClassFactorization
public import ArtinMatthews.SourceQuadraticBadSupport
public import ArtinMatthews.SourceQuadraticLocalSplit
public import ArtinMatthews.SourceQuadraticPairConductor
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

/-! Common-ideal pairs in the same actual local or ray class have
coefficient one on all ideals supported on the fixed source set. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "S" => sourceHilbertSet F S₀
local notation "Bad" => sourceQuadraticBlockBadIdeal F S₀

theorem sourceQuadraticPair_residual_localSquare (b c g : E) (hg : b ⊓ c = g)
    (hclass : sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c)
    (P : HeightOneSpectrum (𝓞 F)) (hP : P ∈ S) :
    ∃ s : P.adicCompletion F, s ^ 2 = algebraMap F (P.adicCompletion F)
      (sourcePrimeExponentUnit F hζ S₀ ((b - g) + (c - g)) : F) :=
  sourceQuadraticLocalClass_eq_localSquare F S₀ hζ (b - g) (c - g)
    (sourceQuadraticPair_residual_localClass F S₀ hζ b c g hg hclass) P hP

theorem sourceQuadraticPair_residual_localSquare_of_rayClass (b c g : E) (hg : b ⊓ c = g)
    (hclass : sourcePrimeExponentRayClass F S₀ b = sourcePrimeExponentRayClass F S₀ c)
    (P : HeightOneSpectrum (𝓞 F)) (hP : P ∈ S) :
    ∃ s : P.adicCompletion F, s ^ 2 = algebraMap F (P.adicCompletion F)
      (sourcePrimeExponentUnit F hζ S₀ ((b - g) + (c - g)) : F) :=
  sourceQuadraticPair_residual_localSquare F S₀ hζ b c g hg
    (sourcePrimeExponentRayClass_eq_localClass F S₀ hζ b c hclass) P hP

variable [IsTotallyComplex F]

theorem sourceQuadraticPair_badPrime_coefficient_one (b c g : E) (hg : b ⊓ c = g)
    (hclass : sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c)
    (P : HeightOneSpectrum (𝓞 F)) (hP : P ∈ S) :
    (sourceQuadraticRayCharacter F S₀ hζ ((b - g) + (c - g))).allCoefficient P.asIdeal = 1 :=
  sourceQuadraticRayCharacter_prime_of_localSquare F S₀ hζ _ P
    (sourceQuadraticPair_residual_localSquare F S₀ hζ b c g hg hclass P hP)

theorem sourceQuadraticPair_badPrime_coefficient_one_of_rayClass
    (b c g : E) (hg : b ⊓ c = g)
    (hclass : sourcePrimeExponentRayClass F S₀ b = sourcePrimeExponentRayClass F S₀ c)
    (P : HeightOneSpectrum (𝓞 F)) (hP : P ∈ S) :
    (sourceQuadraticRayCharacter F S₀ hζ ((b - g) + (c - g))).allCoefficient P.asIdeal = 1 :=
  sourceQuadraticPair_badPrime_coefficient_one F S₀ hζ b c g hg
    (sourcePrimeExponentRayClass_eq_localClass F S₀ hζ b c hclass) P hP

theorem sourceQuadraticPair_supported_coefficient_one (b c g : E) (hg : b ⊓ c = g)
    (hclass : sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c)
    (J : Ideal (𝓞 F)) (hJ : J ≠ ⊥)
    (hsupport : ∀ P : HeightOneSpectrum (𝓞 F), P.asIdeal ∣ J → P ∈ S) :
    (sourceQuadraticRayCharacter F S₀ hζ ((b - g) + (c - g))).allCoefficient J = 1 :=
  sourceQuadraticRayCharacter_supported_coefficient_one F S₀ hζ _
    (sourceQuadraticPair_residual_localSquare F S₀ hζ b c g hg hclass) J hJ hsupport

theorem sourceQuadraticPair_badIdeal_pow_coefficient_one (b c g : E) (hg : b ⊓ c = g)
    (hclass : sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c)
    (n : ℕ) (J : Ideal (𝓞 F)) (hJ : J ∣ Bad ^ n) :
    (sourceQuadraticRayCharacter F S₀ hζ ((b - g) + (c - g))).allCoefficient J = 1 :=
  sourceQuadraticRayCharacter_badIdeal_pow_coefficient_one F S₀ hζ _
    (sourceQuadraticPair_residual_localSquare F S₀ hζ b c g hg hclass) n J hJ

theorem sourceQuadraticPair_badIdeal_coefficient_one (b c g : E) (hg : b ⊓ c = g)
    (hclass : sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c)
    (J : Ideal (𝓞 F)) (hJ : J ∣ Bad) :
    (sourceQuadraticRayCharacter F S₀ hζ ((b - g) + (c - g))).allCoefficient J = 1 :=
  sourceQuadraticRayCharacter_badIdeal_coefficient_one F S₀ hζ _
    (sourceQuadraticPair_residual_localSquare F S₀ hζ b c g hg hclass) J hJ

theorem sourceQuadraticPair_badIdeal_pow_coefficient_one_of_rayClass
    (b c g : E) (hg : b ⊓ c = g)
    (hclass : sourcePrimeExponentRayClass F S₀ b = sourcePrimeExponentRayClass F S₀ c)
    (n : ℕ) (J : Ideal (𝓞 F)) (hJ : J ∣ Bad ^ n) :
    (sourceQuadraticRayCharacter F S₀ hζ ((b - g) + (c - g))).allCoefficient J = 1 :=
  sourceQuadraticPair_badIdeal_pow_coefficient_one F S₀ hζ b c g hg
    (sourcePrimeExponentRayClass_eq_localClass F S₀ hζ b c hclass) n J hJ

theorem sourceQuadraticPair_badIdeal_coefficient_one_of_rayClass
    (b c g : E) (hg : b ⊓ c = g)
    (hclass : sourcePrimeExponentRayClass F S₀ b = sourcePrimeExponentRayClass F S₀ c)
    (J : Ideal (𝓞 F)) (hJ : J ∣ Bad) :
    (sourceQuadraticRayCharacter F S₀ hζ ((b - g) + (c - g))).allCoefficient J = 1 :=
  sourceQuadraticPair_badIdeal_coefficient_one F S₀ hζ b c g hg
    (sourcePrimeExponentRayClass_eq_localClass F S₀ hζ b c hclass) J hJ

end
end ArtinMatthews.SourceEulerAssembly
