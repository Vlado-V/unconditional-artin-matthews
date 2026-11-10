module

public import ArtinMatthews.SourceQuadraticConductor
public import ArtinMatthews.PrincipalAngularCorrection
public import ArtinMatthews.SourcePrimeExponentProducts
public import ArtinMatthews.SourceQuadraticHeckeSymbols
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The primitive global quadratic character has the literal reflected
exterior Euler coefficients, including zeros at shared primes. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic
open AngularLambda
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀

theorem sourceQuadraticConductor_prime_coprime_iff (e : E) (he : ∀ P, e P ≤ 1)
    (P : SourceExteriorPrime F S₀) :
    IsCoprime P.val.asIdeal (sourceQuadraticConductor F S₀ hζ e) ↔ e P = 0 := by
  have hmem : P.val ∈ (integralIdealFiniteModulus (sourceQuadraticConductor F S₀ hζ e)
      (sourceQuadraticConductor_ne_bot F S₀ hζ e)).support ↔
      P.val.asIdeal ∣ sourceQuadraticConductor F S₀ hζ e :=
    integralIdealFiniteModulus_mem_support _ _ P.val
  have hnot : e P = 0 ↔ ¬ P.val.asIdeal ∣ sourceQuadraticConductor F S₀ hζ e := by
    rw [← hmem, Finsupp.mem_support_iff, sourceQuadraticConductor_exterior F S₀ hζ e he P, not_not]
  constructor
  · intro hc
    apply hnot.mpr
    intro hd
    exact P.val.prime.not_isUnit (hc.isUnit_of_dvd' (dvd_refl _) hd)
  · intro hz
    apply principalAngular_prime_coprime_of_not_le P.val
    exact fun hle => hnot.mp hz (Ideal.dvd_iff_le.mpr hle)

variable [IsTotallyComplex F]

theorem sourceQuadraticRayCharacter_prime (e : E) (he : ∀ P, e P ≤ 1)
    (P : SourceExteriorPrime F S₀) :
    (sourceQuadraticRayCharacter F S₀ hζ e).allCoefficient P.val.asIdeal =
      sourceReflectionQuadraticSymbol F S₀ hζ (Finsupp.single P 1) e := by
  unfold EvenIdealRayCharacter.allCoefficient
  rw [dite_eq_left P.val.ne_bot]
  by_cases hp : e P = 0
  · rw [ite_eq_left ((sourceQuadraticConductor_prime_coprime_iff F S₀ hζ e he P).mpr hp),
      sourceQuadraticRayCharacter_idealHom, GaloisIdealCharacter.idealHom_prime]
    exact sourceQuadraticPrimeFrobenius_eq_symbol F S₀ hζ e P hp
  · rw [ite_eq_right (mt (sourceQuadraticConductor_prime_coprime_iff F S₀ hζ e he P).mp hp)]
    symm
    apply Classical.byContradiction
    intro hn
    have hd := (sourceReflectionQuadraticSymbol_ne_zero_iff F S₀ hζ (Finsupp.single P 1) e).mp hn
    exact Finset.disjoint_left.mp hd (by simp) (Finsupp.mem_support_iff.mpr hp)

theorem sourceQuadraticRayCharacter_single (e : E) (he : ∀ P, e P ≤ 1)
    (P : SourceExteriorPrime F S₀) (n : ℕ) :
    (sourceQuadraticRayCharacter F S₀ hζ e).allCoefficient
        (sourcePrimeExponentIdeal F S₀ (Finsupp.single P n)) =
      sourceReflectionQuadraticSymbol F S₀ hζ (Finsupp.single P n) e := by
  induction n with
  | zero =>
      simp only [Finsupp.single_zero]
      simpa [sourcePrimeExponentIdeal, Finsupp.prod, sourceReflectionQuadraticSymbol,
        reflectionExponentResidueValue, sourcePrimeExponentWeight] using
        (sourceQuadraticRayCharacter F S₀ hζ e).allCoefficient_one
  | succ n ih =>
      rw [show Finsupp.single P (n + 1) = Finsupp.single P n + Finsupp.single P 1 from
        Finsupp.single_add P n 1, sourcePrimeExponentIdeal_add,
        EvenIdealRayCharacter.allCoefficient_mul, sourceReflectionQuadraticSymbol,
        sourceReflectionQuadraticSymbol_add_left, ih]
      congr 1
      have hI : sourcePrimeExponentIdeal F S₀ (Finsupp.single P 1) = P.val.asIdeal := by
        change (Finsupp.single P (1 : ℕ)).prod (fun Q n => Q.val.asIdeal ^ n) = _
        rw [Finsupp.prod_single_index (a := P) (b := 1)
          (h := fun Q n => Q.val.asIdeal ^ n) (pow_zero P.val.asIdeal), pow_one]
      simpa only [hI, sourceReflectionQuadraticSymbol] using sourceQuadraticRayCharacter_prime F S₀ hζ e he P

theorem sourceQuadraticRayCharacter_allCoefficient (e : E) (he : ∀ P, e P ≤ 1) (d : E) :
    (sourceQuadraticRayCharacter F S₀ hζ e).allCoefficient (sourcePrimeExponentIdeal F S₀ d) =
      sourceReflectionQuadraticSymbol F S₀ hζ d e := by
  induction d using Finsupp.induction with
  | zero =>
      simpa [sourcePrimeExponentIdeal, Finsupp.prod, sourceReflectionQuadraticSymbol,
        reflectionExponentResidueValue, sourcePrimeExponentWeight] using
        (sourceQuadraticRayCharacter F S₀ hζ e).allCoefficient_one
  | @single_add P n d _ _ ih =>
      rw [sourcePrimeExponentIdeal_add, EvenIdealRayCharacter.allCoefficient_mul,
        sourceReflectionQuadraticSymbol, sourceReflectionQuadraticSymbol_add_left,
        sourceQuadraticRayCharacter_single F S₀ hζ e he P n, ih]
      rfl

end
end ArtinMatthews.SourceEulerAssembly
