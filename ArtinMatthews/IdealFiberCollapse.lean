module

public import ArtinMatthews.IdealFiniteFrame
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Finite weighted Cauchy--Schwarz on numeric fibers, retaining arbitrary
functions of the complete ordered tuple. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {Ω : Type*} [Fintype Ω]

def idealFiberMass (μ : Ω → ℝ) (p : Ω → ℕ) (n : ℕ) : ℝ :=
  ∑ a, if p a = n then μ a else 0

def idealFiberCoefficient (μ : Ω → ℝ) (p : Ω → ℕ) (f : Ω → ℂ) (n : ℕ) : ℂ :=
  ∑ a, if p a = n then (μ a : ℂ) * f a else 0

theorem idealFiberCoefficient_sq_le (μ : Ω → ℝ) (hμ : ∀ a, 0 ≤ μ a)
    (p : Ω → ℕ) (f : Ω → ℂ) (n : ℕ) :
    ‖idealFiberCoefficient μ p f n‖^2 ≤ idealFiberMass μ p n *
      ∑ a, if p a = n then μ a * ‖f a‖^2 else 0 := by
  let w : Ω → ℝ := fun a => if p a = n then μ a else 0
  have hw (a : Ω) : 0 ≤ w a := by
    dsimp [w]
    split_ifs
    · exact hμ a
    · exact le_rfl
  have hc := idealFrame_weighted_cauchy w hw (fun _ => 1) f
  simp only [star_one, mul_one, idealFrameEnergy, norm_one, one_pow] at hc
  have hwcast (a : Ω) : (w a : ℂ) * f a = if p a = n then (μ a : ℂ)*f a else 0 := by
    dsimp [w]
    split_ifs
    · rfl
    · rw [Complex.ofReal_zero, zero_mul]
  simp_rw [hwcast] at hc
  simpa only [idealFiberCoefficient, idealFiberMass, w, ite_mul, zero_mul] using hc

theorem idealFiberCoefficient_energy_le (μ : Ω → ℝ) (hμ : ∀ a, 0 ≤ μ a)
    (p : Ω → ℕ) (f : Ω → ℂ) (S : Finset ℕ) {R : ℝ} (hR : 0 ≤ R)
    (hatom : ∀ n ∈ S, idealFiberMass μ p n ≤ R) :
    (∑ n ∈ S, ‖idealFiberCoefficient μ p f n‖^2) ≤ R * idealFrameEnergy μ f := by
  calc
    _ ≤ ∑ n ∈ S, R * ∑ a, if p a = n then μ a * ‖f a‖^2 else 0 := by
      apply sum_le_sum
      intro n hn
      exact (idealFiberCoefficient_sq_le μ hμ p f n).trans
        (mul_le_mul_of_nonneg_right (hatom n hn) (sum_nonneg fun a _ => by
          split_ifs
          · exact mul_nonneg (hμ a) (sq_nonneg _)
          · exact le_rfl))
    _ = R * ∑ a, ∑ n ∈ S, if p a = n then μ a * ‖f a‖^2 else 0 := by
      rw [← mul_sum, sum_comm]
    _ ≤ R * idealFrameEnergy μ f := by
      apply mul_le_mul_of_nonneg_left _ hR
      unfold idealFrameEnergy
      apply sum_le_sum
      intro a _
      simp only [sum_ite_eq]
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (hμ a) (sq_nonneg _)

end
end ArtinMatthews
