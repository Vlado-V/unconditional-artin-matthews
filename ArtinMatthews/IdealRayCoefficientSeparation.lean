module

public import ArtinMatthews.VaryingKummerAnalyticRayIdealSeries
public import ArtinMatthews.VaryingKummerAnalyticRayIdealMultiplicativity
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

/-! Equality of full coefficient functions implies equality of ideal
values only where both actual conductor masks are nonzero. -/
namespace ArtinMatthews.VaryingKummerAnalytic.EvenIdealRayCharacter
open NumberField
open scoped NumberField nonZeroDivisors
noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem idealHom_eq_of_coefficient_eq_of_coprime {M f : Ideal (𝓞 K)}
    (ψ : EvenIdealRayCharacter K M) (φ : EvenIdealRayCharacter K f)
    (he : ψ.coefficient=φ.coefficient) (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (hM : IsCoprime I M) (hf : IsCoprime I f) :
    ψ.idealHom (integralIdealFractionalUnit I hI)=φ.idealHom (integralIdealFractionalUnit I hI) := by
  have hc : ψ.allCoefficient I=φ.allCoefficient I :=
    (ψ.allCoefficient_eq_coefficient I hI).trans
      ((congrFun he _).trans (φ.allCoefficient_eq_coefficient I hI).symm)
  simp only [allCoefficient,dite_eq_left hI,ite_eq_left hM,ite_eq_left hf] at hc
  exact Units.ext hc

end
end ArtinMatthews.VaryingKummerAnalytic.EvenIdealRayCharacter
