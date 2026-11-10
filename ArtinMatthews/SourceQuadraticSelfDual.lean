module

public import ArtinMatthews.SourceQuadraticConductor
public import ArtinMatthews.SourceQuadraticPrimitive
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

/-! Literal self-duality of the actual primitive source characters,
including their conductor-zero masks. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField VaryingKummerAnalytic
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceQuadraticRayCharacter_star_idealHom (e : SourcePrimeExponents F S₀)
    (I : FractionalIdealGroup F) :
    star ((sourceQuadraticRayCharacter F S₀ hζ e).idealHom I : ℂ) =
      ((sourceQuadraticRayCharacter F S₀ hζ e).idealHom I : ℂ) := by
  have h : ((sourceQuadraticRayCharacter F S₀ hζ e).idealHom I : ℂ) ^ 2 = 1 :=
    congrArg Units.val (sourceQuadraticRayCharacter_sq F S₀ hζ e I)
  rcases sq_eq_one_iff.mp h with heq | heq
  · rw [heq, star_one]
  · rw [heq, star_neg, star_one]

theorem sourceQuadraticRayCharacter_star_allCoefficient (e : SourcePrimeExponents F S₀)
    (I : Ideal (𝓞 F)) :
    star ((sourceQuadraticRayCharacter F S₀ hζ e).allCoefficient I) =
      (sourceQuadraticRayCharacter F S₀ hζ e).allCoefficient I := by
  unfold EvenIdealRayCharacter.allCoefficient
  split_ifs
  · exact sourceQuadraticRayCharacter_star_idealHom F S₀ hζ e _
  · exact star_zero _
  · exact star_zero _

end
end ArtinMatthews.SourceEulerAssembly
