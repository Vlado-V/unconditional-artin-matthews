module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import ArtinMatthews.ShiftedDiagonalFiber
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
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
public import OAI.NumberTheory.Jacobsthal.Sieve.DivisorLogGrowth


set_option backward.privateInPublic true
@[expose] public section

/-! Subpower diagonal bound after exact product-fiber counting. -/

noncomputable section
open scoped BigOperators
namespace ArtinMatthews

theorem shiftedDiagonal_divisor_bound (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ M T : ℕ,
      (∑ k∈Finset.Icc 2 (M*T+1),
        ((k-1).divisors.card : ℝ)*(k.divisors.card : ℝ)^2) ≤
      C*((M*T+1 : ℕ) : ℝ)^(1+ε) := by
  obtain ⟨C₁,hC₁,h₁⟩ := OAI.Erdos970.ErdosDivisorBounds.divisor_power_subpower 1
    (show 0<ε/2 by linarith)
  obtain ⟨C₂,hC₂,h₂⟩ := OAI.Erdos970.ErdosDivisorBounds.divisor_power_subpower 2
    (show 0<ε/2 by linarith)
  refine ⟨C₁*C₂,mul_pos hC₁ hC₂,?_⟩
  intro M T
  let X : ℕ := M*T+1
  have hX : (0 : ℝ)<X := by dsimp [X]; positivity
  have hpoint : ∀ k∈Finset.Icc 2 X,
      ((k-1).divisors.card : ℝ)*(k.divisors.card : ℝ)^2 ≤
        (C₁*C₂)*(X : ℝ)^ε := by
    intro k hk
    obtain ⟨hk₂,hkX⟩ := Finset.mem_Icc.mp hk
    have hkm : k-1≤X := (Nat.sub_le k 1).trans hkX
    have hfirst : ((k-1).divisors.card : ℝ) ≤ C₁*(X : ℝ)^(ε/2) := by
      have h := h₁ (k-1) (by omega)
      simp only [pow_one] at h
      exact h.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hkm) (by positivity)) hC₁.le)
    have hsecond : (k.divisors.card : ℝ)^2 ≤ C₂*(X : ℝ)^(ε/2) :=
      (h₂ k (by omega)).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hkX) (by positivity)) hC₂.le)
    calc
      _ ≤ (C₁*(X : ℝ)^(ε/2))*(C₂*(X : ℝ)^(ε/2)) :=
        mul_le_mul hfirst hsecond (sq_nonneg _) (by positivity)
      _ = (C₁*C₂)*(X : ℝ)^ε := by
        rw [show ε=ε/2+ε/2 by ring,Real.rpow_add hX]
        ring
  have hcard : ((Finset.Icc 2 X).card : ℝ)≤X := by
    exact_mod_cast (show (Finset.Icc 2 X).card≤X by rw [Nat.card_Icc]; omega)
  calc
    _ ≤ ∑ _k∈Finset.Icc 2 X, (C₁*C₂)*(X : ℝ)^ε :=
      Finset.sum_le_sum hpoint
    _ = ((Finset.Icc 2 X).card : ℝ)*((C₁*C₂)*(X : ℝ)^ε) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ (X : ℝ)*((C₁*C₂)*(X : ℝ)^ε) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (C₁*C₂)*(X : ℝ)^(1+ε) := by rw [Real.rpow_add hX,Real.rpow_one]; ring

/-- A general coefficient-sequence consequence, ready to specialize only
after its actual divisor majorant has been proved. -/
theorem shiftedDiagonal_norm_bound (a : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖≤(n.divisors.card : ℝ)) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ M T : ℕ,
      (∑ m∈Finset.Icc 1 M, ∑ n∈Finset.Icc 1 T, ‖a (m*n+1)‖^2) ≤
      C*((M*T+1 : ℕ) : ℝ)^(1+ε) := by
  obtain ⟨C,hC,hbound⟩ := shiftedDiagonal_divisor_bound ε hε
  refine ⟨C,hC,?_⟩
  intro M T
  apply (shiftedProduct_sum_le_divisors M T (fun k => ‖a k‖^2)
    (fun _ => sq_nonneg _)).trans
  apply le_trans _ (hbound M T)
  apply Finset.sum_le_sum
  intro k _hk
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (ha k) 2)
    (Nat.cast_nonneg _)

end ArtinMatthews
