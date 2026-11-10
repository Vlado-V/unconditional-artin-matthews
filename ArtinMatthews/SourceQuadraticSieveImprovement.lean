module

public import ArtinMatthews.SourceQuadraticB3PoissonBound
public import ArtinMatthews.SourceQuadraticPoissonReduction
public import ArtinMatthews.SourceQuadraticScaleEnlargement
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

/-! The explicit improved exponent for the actual exterior energy,
derived from the annular B3 estimate at the original exponent. -/
namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain StandardAdelic
open scoped NumberField

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {G : Type} [Fintype G] [DecidableEq G]

theorem sourceQuadraticDyadicEnergy_improve_of_B3
    (htrace : traceBadPlaces F ⊆ sourceHilbertSet F S₀)
    (label : SourcePrimeExponents F S₀ → G) {a : ℝ} (ha : 1 < a)
    (hE : QuadraticHeckeSieveExponentBound (sourceQuadraticDyadicEnergy F S₀ hζ) a)
    (hB3 : SourceQuadraticB3PoissonBound F S₀ hζ label a) :
    QuadraticHeckeSieveExponentBound (sourceQuadraticDyadicEnergy F S₀ hζ) (2 - a⁻¹) := by
  obtain ⟨A, hA, hscale⟩ := sourceQuadraticDyadicEnergy_enlarge F S₀ hζ htrace
  exact quadraticHeckeSieveExponentBound_of_poisson_scale
    (sourceQuadraticDyadicEnergy F S₀ hζ) ha A hA (2 * Module.finrank ℚ F) hscale
    (sourceQuadraticPoissonScaleBound_of_B3 F S₀ hζ label ha hE hB3)

end ArtinMatthews.SourceEulerAssembly
