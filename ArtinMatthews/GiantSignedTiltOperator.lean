module

public import ArtinMatthews.IdealLabelOperator
public import ArtinMatthews.GiantSignedTiltDensity
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

/-! Changing the fresh law is exactly a multiplier in the literal ideal
coefficient. The auxiliary law remains the original law. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem idealPatternApplyWithLaws_tilt
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}
    (μ r : ∀ j, P j → ℝ) (C : J → Finset (Fin k)) (Θ ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient P C ell)
    (f : MarkedPhysicalMarking P (k+ell) → ℂ) (a : MarkedPhysicalMarking P (k+ell)) :
    idealPatternApplyWithLaws (fun j p => μ j p * r j p) μ C Θ ζ K f a =
      idealPatternApplyWithLaws μ μ C Θ ζ
        (fun a b aux => K a b aux * (idealFreshTargetMass r C b : ℂ)) f a := by
  classical
  unfold idealPatternApplyWithLaws
  apply Finset.sum_congr rfl
  intro aux _
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  split_ifs
  · rw [idealFreshTargetMass_mul, Complex.ofReal_mul]
    ring
  · rfl

theorem idealOperatorWithLaws_tilt
    {I J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}
    (μ r : ∀ j, P j → ℝ) (patterns : Finset I)
    (C : I → J → Finset (Fin k)) (Θ ζ : ℝ)
    (K : ∀ v, GiantTwoSidedPatternCoefficient P (C v) ell)
    (f : MarkedPhysicalMarking P (k+ell) → ℂ) :
    idealOperatorWithLaws (k := k) (ell := ell) (fun j p => μ j p * r j p) μ patterns C Θ ζ K f =
      idealOperatorWithLaws (k := k) (ell := ell) μ μ patterns C Θ ζ
        (fun v (a b : MarkedPhysicalMarking P (k+ell)) aux =>
          K v a b aux * (idealFreshTargetMass (ell := ell) r (C v) b : ℂ)) f := by
  classical
  funext a
  unfold idealOperatorWithLaws
  apply congrArg (fun F : MarkedPhysicalMarking P (k+ell) → ℂ => idealSlotAverage F a)
  funext b
  apply Finset.sum_congr rfl
  intro v _
  exact idealPatternApplyWithLaws_tilt (ell := ell) μ r (C v) Θ ζ (K v) (idealSlotAverage f) b

theorem idealTiltCoefficient_difference
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}
    (r : ∀ j, P j → ℝ) (C : J → Finset (Fin k))
    (K : GiantTwoSidedPatternCoefficient P C ell)
    (a b : MarkedPhysicalMarking P (k+ell)) (aux : GiantTwoSidedPatternAuxiliary P C) :
    K a b aux * (idealFreshTargetMass r C b : ℂ) - K a b aux =
      K a b aux * ((idealFreshTargetMass r C b - 1 : ℝ) : ℂ) := by
  push_cast
  ring

theorem idealTiltCoefficient_difference_norm
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}
    (r : ∀ j, P j → ℝ) (hr : ∀ j p, 1 ≤ r j p)
    (C : J → Finset (Fin k)) (K : GiantTwoSidedPatternCoefficient P C ell)
    (T : ℝ) (hT : ∀ b : MarkedPhysicalMarking P (k+ell), idealFreshTargetMass r C b ≤ T)
    (a b : MarkedPhysicalMarking P (k+ell)) (aux : GiantTwoSidedPatternAuxiliary P C) :
    ‖K a b aux * (idealFreshTargetMass r C b : ℂ) - K a b aux‖ ≤
      ‖K a b aux‖ * (T - 1) := by
  rw [idealTiltCoefficient_difference, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr (idealFreshTargetMass_one_le r hr C b))]
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right (hT b) 1) (norm_nonneg _)

end
end ArtinMatthews
