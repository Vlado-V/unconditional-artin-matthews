module

public import ArtinMatthews.SourceQuadraticConductor
public import ArtinMatthews.ArtinRaySplitCoefficient
public import ArtinMatthews.QuadraticKummerLocalSquare
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
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

/-! A square in the actual completed base field gives coefficient one
for the source quadratic character at that prime. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain VaryingKummerAnalytic AngularLambda
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceQuadraticRayCharacter_prime_of_localSquare
    (e : SourcePrimeExponents F S₀) (P : HeightOneSpectrum (𝓞 F))
    (hsquare : ∃ s : P.adicCompletion F,
      s ^ 2 = algebraMap F (P.adicCompletion F) (sourcePrimeExponentUnit F hζ S₀ e : F)) :
    (sourceQuadraticRayCharacter F S₀ hζ e).allCoefficient P.asIdeal = 1 := by
  let : Algebra F ℂ := sourceComplexAlgebra hζ
  let : IsAbelianGalois F (SourceQuadraticField F S₀ hζ e) :=
    sourceQuadraticField_isAbelianGalois F S₀ hζ e
  exact ArtinRay.abelianNormConductorRayCharacter_prime_of_splitsCompletely
    (sourceQuadraticGaloisCharacter F S₀ hζ e) P
    (quadraticKummer_finitePlaceSplitsCompletely_of_localSquare
      (sourcePrimitiveRootSix F hζ) (sourcePrimeExponentUnit F hζ S₀ e) P hsquare)

end
end ArtinMatthews.SourceEulerAssembly
