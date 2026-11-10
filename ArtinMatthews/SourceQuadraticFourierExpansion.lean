module

public import ArtinMatthews.SourceQuadraticResidueCharacter
public import ArtinMatthews.QuadraticHeckeReducedFourier
public import ArtinMatthews.SourcePoissonAdditiveMass
public import ArtinMatthews.SourceReducedFractionTraceLift
public import ArtinMatthews.ReflectionCoefficientGaussCRT
public import ArtinMatthews.SourceProductPhasePrimitive
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

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators SIntegerPrincipalization
open SIntegerQuotient SourceCRTNormalization StandardAdelic VaryingKummerAnalytic SourcePhysical
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "T" => sourceHilbertSeed F S₀
local notation "OS" => PrincipalIntegerRing T
local notation "S" => sourceHilbertSet F S₀
local notation "E" => ReflectionSquarefreeExponents F S₀
local notation "a" => (sourcePrimeExponentGenerator F hζ S₀ : SourcePrimeExponents F S₀ → OS)
local notation "ha" => sourcePrimeExponentGenerator_ne_zero F hζ S₀
local notation "U" e => (OS ⧸ (Ideal.span {a e} : Ideal OS))ˣ

private theorem sourceQuadraticPhase_primitive_congr (x y : OS) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x = y) (hp : (sIntegerQuotientPhase F S x hx).IsPrimitive) :
    (sIntegerQuotientPhase F S y hy).IsPrimitive := by
  subst y
  exact hp

theorem sourceQuadraticPhase_primitive (htrace : traceBadPlaces F ⊆ S) (e : E) :
    (sIntegerQuotientPhase F S (a e.val) (ha e.val)).IsPrimitive := by
  let P (i : e.val.support) := i.val.val
  let b (i : e.val.support) : OS := sourceAllowedPrimeGenerator F hζ S₀ i.val
  have hP : Pairwise fun i j => P i ≠ P j :=
    fun _ _ hij he => hij (Subtype.ext (Subtype.ext he))
  have hb (i : e.val.support) :
      (P i).asIdeal.map (algebraMap (𝓞 F) OS) = Ideal.span {b i} :=
    sourceAllowedPrimeGenerator_ideal F hζ S₀ i.val
  have hp := sourceProductQuotientPhase_primitive T P hP (fun i => i.val.property) b hb
    (fun _ => 1) (fun i hi => i.val.property (htrace hi))
  exact sourceQuadraticPhase_primitive_congr F S₀ _ _ _ _
    (reflectionSquarefreeGenerator_support F hζ S₀ e).symm hp

def sourceQuadraticFourierWeight (e : E) (d : U e.val) : ℂ := by
  let : Finite (OS ⧸ (Ideal.span {a e.val} : Ideal OS)) :=
    sourcePrimeExponentGenerator_quotient_finite F hζ S₀ e.val
  let := Fintype.ofFinite (OS ⧸ (Ideal.span {a e.val} : Ideal OS))
  exact primitiveReducedFourierWeight (sourceReflectionQuadraticCharacter F S₀ hζ e)
    (sIntegerQuotientPhase F S (a e.val) (ha e.val)) d

theorem sourceQuadraticFourierWeight_mass (htrace : traceBadPlaces F ⊆ S) (e : E) :
    letI := sourcePoissonQuotientUnitFintype F S₀ hζ e.val
    (∑ d : U e.val, ‖sourceQuadraticFourierWeight F S₀ hζ e d‖ ^ 2) ≤ 1 := by
  let : Finite (OS ⧸ (Ideal.span {a e.val} : Ideal OS)) :=
    sourcePrimeExponentGenerator_quotient_finite F hζ S₀ e.val
  let := Fintype.ofFinite (OS ⧸ (Ideal.span {a e.val} : Ideal OS))
  exact primitiveReducedFourierWeight_mass (sourceReflectionQuadraticCharacter F S₀ hζ e)
    (sourceReflectionQuadraticCharacter_primitive F S₀ hζ e)
    (sIntegerQuotientPhase F S (a e.val) (ha e.val))
    (sourceQuadraticPhase_primitive F S₀ hζ htrace e)

/-- The actual quadratic residue value is the sum of its reduced additive
phases, with total Fourier coefficient square mass at most one. -/
theorem sourceQuadraticFourierExpansion (htrace : traceBadPlaces F ⊆ S) (e : E) (m : OS) :
    letI := sourcePoissonQuotientUnitFintype F S₀ hζ e.val
    reflectionExponentResidueValue F hζ S₀ e.val m ^ 3 =
      ∑ d : U e.val, sourceQuadraticFourierWeight F S₀ hζ e d *
        sourceReducedFractionPhase F S₀ a ha ⟨e.val, d⟩ m := by
  let : Finite (OS ⧸ (Ideal.span {a e.val} : Ideal OS)) :=
    sourcePrimeExponentGenerator_quotient_finite F hζ S₀ e.val
  let := Fintype.ofFinite (OS ⧸ (Ideal.span {a e.val} : Ideal OS))
  exact (sourceReflectionQuadraticCharacter_apply F S₀ hζ e m).symm.trans
    (primitiveReducedFourierExpansion (sourceReflectionQuadraticCharacter F S₀ hζ e)
      (sourceReflectionQuadraticCharacter_primitive F S₀ hζ e)
      (sIntegerQuotientPhase F S (a e.val) (ha e.val))
      (sourceQuadraticPhase_primitive F S₀ hζ htrace e) (Ideal.Quotient.mk _ m))

end
end ArtinMatthews.SourceEulerAssembly
