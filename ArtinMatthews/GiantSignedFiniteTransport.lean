module

public import Mathlib.Analysis.Complex.Norm
public import ArtinMatthews.IdealProductAverage
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

/-! Weighted finite transport with its exact input and output masses. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem giantSignedFiniteTransport_energy
    {X Y : Type*} [Fintype X] [Fintype Y]
    (sourceMass : X → ℝ) (targetMass : Y → ℝ) (q : X → Y → ℝ)
    (hsource : ∀ x, 0 ≤ sourceMass x) (hq : ∀ x y, 0 ≤ q x y)
    (hrow : ∀ x, ∑ y, q x y = 1)
    (hpush : ∀ y, ∑ x, sourceMass x * q x y = targetMass y)
    (K : X → Y → ℂ) (C : ℝ) (hK : ∀ x y, ‖K x y‖ ≤ C) (f : Y → ℂ) :
    (∑ x, sourceMass x * ‖∑ y, (q x y : ℂ) * K x y * f y‖ ^ 2) ≤
      C ^ 2 * ∑ y, targetMass y * ‖f y‖ ^ 2 := by
  classical
  have hp (x : X) : ‖∑ y, (q x y : ℂ) * K x y * f y‖ ^ 2 ≤
      ∑ y, q x y * (C ^ 2 * ‖f y‖ ^ 2) := by
    have hj := idealWeightedJensen (q x) (hq x) (hrow x) (fun y => K x y * f y)
    simp only [← mul_assoc] at hj
    apply hj.trans
    apply Finset.sum_le_sum
    intro y _
    apply mul_le_mul_of_nonneg_left _ (hq x y)
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans (hK x y))).mpr (hK x y))
      (sq_nonneg ‖f y‖)
  calc
    _ ≤ ∑ x, sourceMass x * ∑ y, q x y * (C ^ 2 * ‖f y‖ ^ 2) :=
      Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hp x) (hsource x)
    _ = ∑ y, targetMass y * (C ^ 2 * ‖f y‖ ^ 2) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      simp only [← mul_assoc, ← Finset.sum_mul, hpush]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring

end
end ArtinMatthews
