module

public import ArtinMatthews.QuadraticHeckeScaleOptimizer
public import ArtinMatthews.SourceQuadraticSieveEnergy
public import ArtinMatthews.SourceReflectionExpansion
public import ArtinMatthews.SourceQuadraticScaleEnlargement
public import ArtinMatthews.SourceQuadraticSieveReflection
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

/-! The checked analytic interface between the Poisson-scale bound and
the exterior sieve used by the actual reflected square moment. -/
namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain StandardAdelic
open scoped NumberField

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceReflectionQuadraticSieve_of_poisson
    (htrace : traceBadPlaces F ⊆ sourceHilbertSet F S₀)
    (hpoisson : ∀ a : ℝ, 1 < a →
      QuadraticHeckeSieveExponentBound (sourceQuadraticDyadicEnergy F S₀ hζ) a →
      QuadraticHeckePoissonScaleBound (sourceQuadraticDyadicEnergy F S₀ hζ) a) :
    SourceReflectionQuadraticSieve F S₀ hζ :=
  sourceReflectionQuadraticSieve_of_exponent_one F S₀ hζ htrace
    (sourceQuadraticDyadicEnergy_exponent_one_of_poisson F S₀ hζ htrace hpoisson)

end ArtinMatthews.SourceEulerAssembly
