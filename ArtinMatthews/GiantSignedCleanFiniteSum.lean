module

public import ArtinMatthews.GiantSignedCleanDamping
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

namespace ArtinMatthews
open scoped BigOperators
noncomputable section

/-- Finite weighted sums pass through the actual active-slot average. -/
theorem idealSlotAverage_sum_mul {T J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {M : ℕ} (s : Finset T) (c : T → ℂ)
    (f : T → MarkedPhysicalMarking P M → ℂ) (a : MarkedPhysicalMarking P M) :
    idealSlotAverage (fun b => ∑ t ∈ s, c t * f t b) a =
      ∑ t ∈ s, c t * idealSlotAverage (f t) a := by
  classical
  unfold idealSlotAverage
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro π _
  ring

/-- The literal translated clean pattern preserves finite weighted sums. -/
theorem giantSignedCleanFiberPattern_sum_mul
    {T G J : Type*} [AddCommGroup G] [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k ell : ℕ}
    (freshLaw auxLaw : ∀ j, P j → ℝ) (C : J → Finset (Fin k)) (Θ ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient P C ell) (u : G)
    (s : Finset T) (c : T → ℂ)
    (f : T → G → MarkedPhysicalMarking P (k + ell) → ℂ)
    (x : G) (a : MarkedPhysicalMarking P (k + ell)) :
    giantSignedCleanFiberPattern freshLaw auxLaw C Θ ζ K u
        (fun y b => ∑ t ∈ s, c t * f t y b) x a =
      ∑ t ∈ s, c t * giantSignedCleanFiberPattern freshLaw auxLaw C Θ ζ K u (f t) x a := by
  classical
  unfold giantSignedCleanFiberPattern
  simp only [Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro aux _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hab : IdealCopied C a b
  · simp only [hab, ite_true, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  · simp only [hab, ite_false, mul_zero, Finset.sum_const_zero]

/-- Both original slot averages preserve finite weighted sums through the clean operator. -/
theorem giantSignedCleanFiberApply_sum_mul
    {T I G J : Type*} [AddCommGroup G] [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k ell : ℕ}
    (freshLaw auxLaw : ∀ j, P j → ℝ) (patterns : Finset I)
    (C : I → J → Finset (Fin k)) (Θ ζ : ℝ)
    (K : ∀ v, GiantTwoSidedPatternCoefficient P (C v) ell) (u : G)
    (s : Finset T) (c : T → ℂ)
    (f : T → G → MarkedPhysicalMarking P (k + ell) → ℂ)
    (x : G) (a : MarkedPhysicalMarking P (k + ell)) :
    giantSignedCleanFiberApply freshLaw auxLaw patterns C Θ ζ K u
        (fun y b => ∑ t ∈ s, c t * f t y b) x a =
      ∑ t ∈ s, c t * giantSignedCleanFiberApply freshLaw auxLaw patterns C Θ ζ K u (f t) x a := by
  classical
  have hinner (y : G) :
      idealSlotAverage (fun b => ∑ t ∈ s, c t * f t y b) =
        fun b => ∑ t ∈ s, c t * idealSlotAverage (f t y) b := by
    funext b
    exact idealSlotAverage_sum_mul s c (fun t => f t y) b
  unfold giantSignedCleanFiberApply
  simp_rw [hinner, giantSignedCleanFiberPattern_sum_mul]
  have houter (b : MarkedPhysicalMarking P (k + ell)) :
      (∑ v ∈ patterns, ∑ t ∈ s, c t *
        giantSignedCleanFiberPattern freshLaw auxLaw (C v) Θ ζ (K v) u
          (fun y => idealSlotAverage (f t y)) x b) =
        ∑ t ∈ s, c t * ∑ v ∈ patterns,
          giantSignedCleanFiberPattern freshLaw auxLaw (C v) Θ ζ (K v) u
            (fun y => idealSlotAverage (f t y)) x b := by
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  simp_rw [houter]
  exact idealSlotAverage_sum_mul s c _ a

/-- Both arbitrary damping factors remain in the finite weighted-sum identity. -/
theorem giantSignedDampedCleanFiberApply_sum_mul
    {T I G J : Type*} [AddCommGroup G] [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k ell : ℕ}
    (freshLaw auxLaw : ∀ j, P j → ℝ) (patterns : Finset I)
    (C : I → J → Finset (Fin k)) (Θ ζ : ℝ)
    (K : ∀ v, GiantTwoSidedPatternCoefficient P (C v) ell) (u : G)
    (dIn dOut : G → ℂ) (s : Finset T) (c : T → ℂ)
    (f : T → G → MarkedPhysicalMarking P (k + ell) → ℂ)
    (x : G) (a : MarkedPhysicalMarking P (k + ell)) :
    giantSignedDampedCleanFiberApply freshLaw auxLaw patterns C Θ ζ K u dIn dOut
        (fun y b => ∑ t ∈ s, c t * f t y b) x a =
      ∑ t ∈ s, c t * giantSignedDampedCleanFiberApply freshLaw auxLaw patterns C Θ ζ K u
        dIn dOut (f t) x a := by
  classical
  have hinput : (fun y b => dOut y * ∑ t ∈ s, c t * f t y b) =
      fun y b => ∑ t ∈ s, c t * (dOut y * f t y b) := by
    funext y b
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  unfold giantSignedDampedCleanFiberApply
  rw [hinput, giantSignedCleanFiberApply_sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

end
end ArtinMatthews
