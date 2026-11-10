module

public import ArtinMatthews.SourceQuadraticSieveEnergy
public import ArtinMatthews.SourceReflectionExpansion
public import ArtinMatthews.SourceQuadraticActualB3
public import ArtinMatthews.SourceQuadraticSieveFromB3
public import ArtinMatthews.SourceQuadraticSieveImprovement
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

open NumberField IsDedekindDomain StandardAdelic
open scoped NumberField
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

/-- Actual exponent improvement from the proved source B3 estimate. -/
theorem sourceQuadraticDyadicEnergy_improve_actual
    (htrace : traceBadPlaces F ⊆ sourceHilbertSet F S₀) {α : ℝ} (hα : 1 < α)
    (hE : QuadraticHeckeSieveExponentBound (sourceQuadraticDyadicEnergy F S₀ hζ) α) :
    QuadraticHeckeSieveExponentBound (sourceQuadraticDyadicEnergy F S₀ hζ) (2 - α⁻¹) := by
  classical
  let : Finite (SourceQuadraticRayClass F S₀) := sourceQuadraticRayClass_finite F S₀
  let := Fintype.ofFinite (SourceQuadraticRayClass F S₀)
  exact sourceQuadraticDyadicEnergy_improve_of_B3 F S₀ hζ htrace
    (sourcePrimeExponentRayClass F S₀) hα hE
    (sourceQuadraticB3PoissonBound_actual F S₀ hζ htrace hα.le hE)

/-- The sharp quadratic sieve for the actual source family.  All Poisson,
contour, signed-residue and tail estimates are discharged above. -/
theorem sourceReflectionQuadraticSieve_actual
    (htrace : traceBadPlaces F ⊆ sourceHilbertSet F S₀) :
    SourceReflectionQuadraticSieve F S₀ hζ := by
  classical
  let : Finite (SourceQuadraticRayClass F S₀) := sourceQuadraticRayClass_finite F S₀
  let := Fintype.ofFinite (SourceQuadraticRayClass F S₀)
  exact sourceReflectionQuadraticSieve_of_B3 F S₀ hζ htrace
    (sourcePrimeExponentRayClass F S₀) fun _ hα hE =>
      sourceQuadraticB3PoissonBound_actual F S₀ hζ htrace hα.le hE

end
end ArtinMatthews.SourceEulerAssembly
