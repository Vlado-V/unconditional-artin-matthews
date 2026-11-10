module

public import ArtinMatthews.IdealLabelOperator
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

/-! Coefficient linearity of the literal copied/fresh ideal operator. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem giantSignedIdealSlotAverage_sub {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {M : ℕ} (f g : MarkedPhysicalMarking P M → ℂ)
    (a : MarkedPhysicalMarking P M) :
    idealSlotAverage (fun b => f b - g b) a = idealSlotAverage f a - idealSlotAverage g a := by
  unfold idealSlotAverage
  rw [Finset.sum_sub_distrib, mul_sub]

theorem giantSignedIdealPattern_sub {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k ell : ℕ}
    (freshLaw auxLaw : ∀ j, P j → ℝ) (C : J → Finset (Fin k)) (Θ ζ : ℝ)
    (K L : GiantTwoSidedPatternCoefficient P C ell)
    (f : MarkedPhysicalMarking P (k+ell) → ℂ) (a : MarkedPhysicalMarking P (k+ell)) :
    idealPatternApplyWithLaws freshLaw auxLaw C Θ ζ (fun a b aux => K a b aux - L a b aux) f a =
      idealPatternApplyWithLaws freshLaw auxLaw C Θ ζ K f a -
        idealPatternApplyWithLaws freshLaw auxLaw C Θ ζ L f a := by
  classical
  unfold idealPatternApplyWithLaws
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro aux _
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> ring

theorem giantSignedIdealOperator_sub {I J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k ell : ℕ}
    (freshLaw auxLaw : ∀ j, P j → ℝ) (patterns : Finset I)
    (C : I → J → Finset (Fin k)) (Θ ζ : ℝ)
    (K L : ∀ v, GiantTwoSidedPatternCoefficient P (C v) ell)
    (f : MarkedPhysicalMarking P (k+ell) → ℂ) (a : MarkedPhysicalMarking P (k+ell)) :
    idealOperatorWithLaws freshLaw auxLaw patterns C Θ ζ
        (fun v a b aux => K v a b aux - L v a b aux) f a =
      idealOperatorWithLaws freshLaw auxLaw patterns C Θ ζ K f a -
        idealOperatorWithLaws freshLaw auxLaw patterns C Θ ζ L f a := by
  classical
  unfold idealOperatorWithLaws
  simp_rw [giantSignedIdealPattern_sub, Finset.sum_sub_distrib]
  exact giantSignedIdealSlotAverage_sub _ _ a

end
end ArtinMatthews
