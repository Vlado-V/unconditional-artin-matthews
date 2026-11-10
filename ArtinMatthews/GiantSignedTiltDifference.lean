module

public import ArtinMatthews.GiantSignedMemoryState
public import ArtinMatthews.IdealLabelOperator
public import ArtinMatthews.GiantSignedIdealLinearity
public import ArtinMatthews.GiantSignedTiltDensity
public import ArtinMatthews.GiantSignedTiltOperator
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.NumberTheory.SelbergSieve
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

/-! The fresh-law perturbation is the literal coefficient difference. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem giantSignedIdeal_tilt_difference
    {I J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}
    (μ r : ∀ j, P j → ℝ) (patterns : Finset I)
    (C : I → J → Finset (Fin k)) (Θ ζ : ℝ)
    (K : ∀ v, GiantTwoSidedPatternCoefficient P (C v) ell)
    (f : MarkedPhysicalMarking P (k+ell) → ℂ) (a : MarkedPhysicalMarking P (k+ell)) :
    idealOperatorWithLaws (k := k) (ell := ell) (fun j p => μ j p * r j p) μ
        patterns C Θ ζ K f a - idealOperatorWithLaws μ μ patterns C Θ ζ K f a =
      idealOperatorWithLaws (k := k) (ell := ell) μ μ patterns C Θ ζ
        (fun v (a b : MarkedPhysicalMarking P (k+ell)) aux =>
          K v a b aux * ((idealFreshTargetMass (ell := ell) r (C v) b - 1 : ℝ) : ℂ)) f a := by
  classical
  let L : ∀ v, GiantTwoSidedPatternCoefficient P (C v) ell :=
    fun v a b aux => K v a b aux * (idealFreshTargetMass r (C v) b : ℂ)
  have he := congrArg (fun g => g a) (idealOperatorWithLaws_tilt μ r patterns C Θ ζ K f)
  change idealOperatorWithLaws (fun j p => μ j p * r j p) μ patterns C Θ ζ K f a =
    idealOperatorWithLaws μ μ patterns C Θ ζ L f a at he
  rw [he, ← giantSignedIdealOperator_sub μ μ patterns C Θ ζ L K f a]
  have hcoeff : (fun v a b aux => L v a b aux - K v a b aux) =
      (fun v a b aux => K v a b aux * ((idealFreshTargetMass r (C v) b - 1 : ℝ) : ℂ)) := by
    funext v a b aux
    exact idealTiltCoefficient_difference r (C v) (K v) a b aux
  rw [hcoeff]

theorem giantSignedTilt_originalEnergy_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {M : ℕ} (μ r : ∀ j, P j → ℝ)
    (hμ : ∀ j p, 0 ≤ μ j p) (hr : ∀ j p, 1 ≤ r j p)
    (f : MarkedPhysicalMarking P M → ℂ) :
    (∑ a, giantSignedActiveMass μ a * ‖f a‖ ^ 2) ≤
      ∑ a, giantSignedActiveMass (fun j p => μ j p * r j p) a * ‖f a‖ ^ 2 := by
  classical
  apply Finset.sum_le_sum
  intro a _
  rw [giantSignedActiveMass_mul]
  have hm : 0 ≤ giantSignedActiveMass μ a :=
    Finset.prod_nonneg fun j _ => Finset.prod_nonneg fun i _ => hμ j (a j i)
  have h := mul_le_mul_of_nonneg_left (giantSignedActiveMass_one_le r hr a)
    (mul_nonneg hm (sq_nonneg ‖f a‖))
  nlinarith

end
end ArtinMatthews
