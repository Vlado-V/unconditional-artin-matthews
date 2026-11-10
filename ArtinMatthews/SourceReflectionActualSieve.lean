module

public import ArtinMatthews.SourcePoissonAngularOfReflected
public import ArtinMatthews.SourceReflectionRowClass
public import ArtinMatthews.SourceQuadraticSieveActual
public import ArtinMatthews.SourceReflectionLiteralMoment
public import ArtinMatthews.SourceReflectionPoissonMoment
public import ArtinMatthews.SourceReflectionTrace
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
open NumberField IsDedekindDomain AllowedGenerators SourcePhysical VaryingKummerAnalytic QuadraticWeil
open Filter Asymptotics
open scoped NumberField Classical BigOperators Topology
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)
variable (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
local notation "E" => SourcePrimeExponents F S₀
local notation "Rows" => SourceNonzeroFrequency F S₀
local notation "Classes" => ExteriorUnitSixthClasses (sourceHilbertSet F S₀)

/-- The literal reflected moment with the actual quadratic sieve discharged. -/
theorem exists_sourceReflectionLiteralMoment_le_actual {U : Type} [Fintype U]
    (A : Classes → SourceReflectionExpansionData F S₀ U)
    (hA : SourceReflectionLiteralExpansion F S₀ hζ η hBad A) {K M ε : ℝ}
    (hK : 1 ≤ K) (hM : 1 ≤ M) (hε : 0 < ε) :
    ∃ cBound : ℝ, 0 < cBound ∧ ∀ Z : ℝ, 1 ≤ Z → ∀ (X : Finset Rows) (L : ℕ),
      (∀ m ∈ X, (sourcePrimeExponentNorm F S₀
        (sourceElementExponents F S₀ m.val m.property) : ℝ) ≤ K * Z ^ M) →
      (∀ e : E, (X.filter (fun m => sourceElementExponents F S₀ m.val m.property = e)).card ≤ L) →
      ∑ m ∈ X, ‖reflectionCoefficientRow F hζ S₀ hBad η m.val Z‖ ^ 2 ≤
        cBound * (L : ℝ) * Z ^ (2 * M - 1 + ε) :=
  exists_sourceReflectionLiteralMoment_le F S₀ hζ η hBad A hA
    (sourceReflectionQuadraticSieve_actual F S₀ hζ (sourceTraceBadPlaces_subset_of_weil F S₀ hBad))
    hK hM hε

/-- The source Poisson reflected moment requires only its literal expansion. -/
theorem sourcePoissonReflectedSecondMoment_of_expansion_actual {U : Type} [Fintype U]
    (A : Classes → SourceReflectionExpansionData F S₀ U)
    (hA : SourceReflectionLiteralExpansion F S₀ hζ η hBad A) :
    SourcePoissonReflectedSecondMoment F S₀ hζ η hBad :=
  sourcePoissonReflectedSecondMoment_of_expansion F S₀ hζ η hBad A hA
    (sourceReflectionQuadraticSieve_actual F S₀ hζ (sourceTraceBadPlaces_subset_of_weil F S₀ hBad))

/-- The actual physical probe bound following from the literal reflected expansion. -/
theorem sourcePoissonPhysicalProbe_bound_of_expansion_actual {U : Type} [Fintype U]
    (v : InfinitePlace F) (A : Classes → SourceReflectionExpansionData F S₀ U)
    (hA : SourceReflectionLiteralExpansion F S₀ hζ η hBad A) :
    sourcePoissonPhysicalProbeAtScales F S₀ hζ η v hBad =O[atTop]
      (fun Z : ℝ => Z ^ (933 / 2000 + 1 / 100000 : ℝ)) :=
  sourcePoissonPhysicalProbe_bound_of_reflected F S₀ hζ η v hBad
    (sourcePoissonReflectedSecondMoment_of_expansion_actual F S₀ hζ η hBad A hA)

/-- The source-infinity exponent following from the literal reflected expansion. -/
theorem sourcePoissonAngularSignal_bound_of_expansion_actual {U : Type} [Fintype U]
    (v : InfinitePlace F) (hJ : J ≠ ⊥)
    (hcut : principalAngularCutoff F J ⊆ sourceHilbertSet F S₀)
    (A : Classes → SourceReflectionExpansionData F S₀ U)
    (hA : SourceReflectionLiteralExpansion F S₀ hζ η hBad A) :
    principalAngularGaussianSignal hζ η (sourceHilbertSet F S₀) =O[atTop]
      (fun Z : ℝ => Z ^ (7 / 15 - 1 / 20000 : ℝ)) :=
  sourcePoissonAngularSignal_bound_of_reflected F S₀ hζ η v hBad hJ hcut
    (sourcePoissonReflectedSecondMoment_of_expansion_actual F S₀ hζ η hBad A hA)

end
end ArtinMatthews.SourceEulerAssembly
