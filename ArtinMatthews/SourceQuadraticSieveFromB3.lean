module

public import ArtinMatthews.SourceQuadraticB3PoissonBound
public import ArtinMatthews.SourceQuadraticPoissonReduction
public import ArtinMatthews.SourceQuadraticSieveFromPoisson
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

/-! The analytic B3 estimate is the remaining input to the literal
sharp quadratic large sieve and the reflected-moment application. -/
namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain StandardAdelic
open scoped NumberField

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {G : Type} [Fintype G] [DecidableEq G]

theorem sourceReflectionQuadraticSieve_of_B3
    (htrace : traceBadPlaces F ⊆ sourceHilbertSet F S₀)
    (label : SourcePrimeExponents F S₀ → G)
    (hB3 : ∀ a : ℝ, 1 < a →
      QuadraticHeckeSieveExponentBound (sourceQuadraticDyadicEnergy F S₀ hζ) a →
      SourceQuadraticB3PoissonBound F S₀ hζ label a) :
    SourceReflectionQuadraticSieve F S₀ hζ :=
  sourceReflectionQuadraticSieve_of_poisson F S₀ hζ htrace fun a ha hE =>
    sourceQuadraticPoissonScaleBound_of_B3 F S₀ hζ label ha hE (hB3 a ha hE)

end ArtinMatthews.SourceEulerAssembly
