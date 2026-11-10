module

public import ArtinMatthews.SourceQuadraticBlockIdeals
public import ArtinMatthews.SourceQuadraticLocalSplit
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

/-! Exact coefficient one on ideals supported on the fixed source set,
including every divisor of a power of its literal denominator ideal. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain VaryingKummerAnalytic SIntegerPrincipalization
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
local notation "S" => sourceHilbertSet F S₀
local notation "Bad" => sourceQuadraticBlockBadIdeal F S₀

theorem sourceQuadraticBlockBadIdeal_ne_bot : Bad ≠ ⊥ :=
  Ideal.span_singleton_eq_bot.not.mpr
    (principalizingDenominator_ne_zero (sourceHilbertSeed F S₀))

theorem sourceQuadraticBlockBadIdeal_prime_dvd_iff (P : HeightOneSpectrum (𝓞 F)) :
    P.asIdeal ∣ Bad ↔ P ∈ S := by
  change P.asIdeal ∣ Ideal.span {principalizingDenominator (sourceHilbertSeed F S₀)} ↔
    P ∈ denominatorSupport (principalizingDenominator (sourceHilbertSeed F S₀))
      (principalizingDenominator_ne_zero (sourceHilbertSeed F S₀))
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem, mem_denominatorSupport]

variable [IsTotallyComplex F] {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀

theorem sourceQuadraticRayCharacter_supported_coefficient_one (e : E)
    (hsquare : ∀ P : HeightOneSpectrum (𝓞 F), P ∈ S →
      ∃ s : P.adicCompletion F,
        s ^ 2 = algebraMap F (P.adicCompletion F) (sourcePrimeExponentUnit F hζ S₀ e : F))
    (J : Ideal (𝓞 F)) (hJ : J ≠ ⊥)
    (hsupport : ∀ P : HeightOneSpectrum (𝓞 F), P.asIdeal ∣ J → P ∈ S) :
    (sourceQuadraticRayCharacter F S₀ hζ e).allCoefficient J = 1 := by
  let d := sourceFullIdealExponents F J
  have hrec : sourceFullExponentIdeal F d = J := sourceFullIdealExponents_recover F J hJ
  rw [← hrec]
  change (sourceQuadraticRayCharacter F S₀ hζ e).coefficientHom
    (∏ P ∈ d.support, P.asIdeal ^ d P) = 1
  rw [map_prod]
  apply Finset.prod_eq_one
  intro P hP
  rw [map_pow]
  have hdiv : P.asIdeal ∣ J := by
    rw [← hrec]
    exact (dvd_pow_self P.asIdeal (Finsupp.mem_support_iff.mp hP)).trans
      (Finset.dvd_prod_of_mem (fun Q => Q.asIdeal ^ d Q) hP)
  change (sourceQuadraticRayCharacter F S₀ hζ e).allCoefficient P.asIdeal ^ d P = 1
  rw [sourceQuadraticRayCharacter_prime_of_localSquare F S₀ hζ e P
    (hsquare P (hsupport P hdiv)), one_pow]

theorem sourceQuadraticRayCharacter_badIdeal_pow_coefficient_one (e : E)
    (hsquare : ∀ P : HeightOneSpectrum (𝓞 F), P ∈ S →
      ∃ s : P.adicCompletion F,
        s ^ 2 = algebraMap F (P.adicCompletion F) (sourcePrimeExponentUnit F hζ S₀ e : F))
    (n : ℕ) (J : Ideal (𝓞 F)) (hJ : J ∣ Bad ^ n) :
    (sourceQuadraticRayCharacter F S₀ hζ e).allCoefficient J = 1 := by
  apply sourceQuadraticRayCharacter_supported_coefficient_one F S₀ hζ e hsquare J
    (ne_zero_of_dvd_ne_zero (pow_ne_zero n (sourceQuadraticBlockBadIdeal_ne_bot F S₀)) hJ)
  intro P hP
  apply (sourceQuadraticBlockBadIdeal_prime_dvd_iff F S₀ P).mp
  exact P.prime.dvd_of_dvd_pow (hP.trans hJ)

theorem sourceQuadraticRayCharacter_badIdeal_coefficient_one (e : E)
    (hsquare : ∀ P : HeightOneSpectrum (𝓞 F), P ∈ S →
      ∃ s : P.adicCompletion F,
        s ^ 2 = algebraMap F (P.adicCompletion F) (sourcePrimeExponentUnit F hζ S₀ e : F))
    (J : Ideal (𝓞 F)) (hJ : J ∣ Bad) :
    (sourceQuadraticRayCharacter F S₀ hζ e).allCoefficient J = 1 := by
  apply sourceQuadraticRayCharacter_badIdeal_pow_coefficient_one F S₀ hζ e hsquare 1 J
  simpa only [pow_one] using hJ

end
end ArtinMatthews.SourceEulerAssembly
