module

public import ArtinMatthews.VaryingKummerAnalyticMixedPrimitiveRayReflection
public import ArtinMatthews.VaryingKummerAnalyticMixedRadialMellin
public import ArtinMatthews.VaryingKummerAnalyticMixedRayClassMellin
public import ArtinMatthews.VaryingKummerAnalyticMixedRayClassSum
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

/-! The exact normalized Mellin sum of the conductor-dual class theta is
the completed actual ideal-ray Dirichlet series in its convergent half-plane. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Module MeasureTheory
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K] {M : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)

theorem mixedConductorDual_class_mellin_sum {s : ℂ} (hs : 1 < s.re) :
    (∑ c : ClassGroup (𝓞 K),
      ((FractionalIdeal.absNorm (mixedTraceDualIdeal K
        (mixedConductorIdeal K (rayClassRepresentative K 1 c) M
          (rayClassRepresentative_ne_bot K 1 c) hM)).val:ℝ):ℂ)^s *
      mellin (fun t => ∫ u in mixedUnitLogDomain K,
        mixedRayClassTheta K ψ
          (mixedTraceDualIdeal K (mixedConductorIdeal K (rayClassRepresentative K 1 c) M
            (rayClassRepresentative_ne_bot K 1 c) hM)) u t)
        ((Module.finrank ℚ K:ℂ)*s/2)) =
      (torsionOrder K:ℂ)*((mixedRadialJacobian K:ℂ)*mixedGammaFactor K s)*ψ.dirichlet s := by
  simp_rw [mixedRayClassTheta_mellin_normalized K ψ _ hs]
  rw [← Finset.mul_sum,ψ.conductorDual_partial_class_sum hM hs]

end
end ArtinMatthews.VaryingKummerAnalytic
