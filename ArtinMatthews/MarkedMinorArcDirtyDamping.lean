module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual repeated pending-index choices are absorbed by the retained
outgoing damping, with no distinct-numeric-value or anchor assumption. -/
namespace ArtinMatthews
open scoped BigOperators

/-- Uniform source index damping for every 0≤rho<1, including n=0. -/
theorem markedMinorDirty_index_damping {ρ : ℝ} (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1) (n : ℕ) :
    (n : ℝ)*ρ^(n-1) ≤ 1/(1-ρ)^2 := by
  cases n with
  | zero => simp only [Nat.cast_zero,zero_mul]; positivity
  | succ n =>
    have hs := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := ρ) 1
      (by simpa only [Real.norm_eq_abs,abs_of_nonneg hρ₀] using hρ₁)
    have hb := sum_le_hasSum ({n} : Finset ℕ) (fun m _ => by positivity) hs
    simpa only [Finset.sum_singleton,Nat.choose_one_right,Nat.cast_add,Nat.cast_one,
      Nat.add_sub_cancel,Nat.reduceAdd] using hb

/-- Selecting one eligible pending index and damping all the other hits is
bounded uniformly even when numeric labels and anchors repeat. -/
theorem markedMinorDirty_pending_choices {ι : Type*} (H : Finset ι)
    {ρ : ℝ} (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1) :
    (∑ _j ∈ H, ρ^(H.card-1)) ≤ 1/(1-ρ)^2 := by
  simpa only [Finset.sum_const,smul_eq_mul,nsmul_eq_mul] using
    markedMinorDirty_index_damping hρ₀ hρ₁ H.card

/-- Newly stored hits only decrease the genuine damping factor. -/
theorem markedMinorDirty_pending_choices_extra {ι : Type*} (H : Finset ι)
    {ρ : ℝ} (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1) (k : ℕ) :
    (∑ _j ∈ H, ρ^(H.card-1+k)) ≤ 1/(1-ρ)^2 := by
  calc
    _ = (∑ _j ∈ H, ρ^(H.card-1))*ρ^k := by simp only [pow_add,Finset.sum_mul]
    _ ≤ (∑ _j ∈ H, ρ^(H.card-1))*1 := mul_le_mul_of_nonneg_left
      (pow_le_one₀ hρ₀ hρ₁.le) (Finset.sum_nonneg (fun _ _ => pow_nonneg hρ₀ _))
    _ = ∑ _j ∈ H, ρ^(H.card-1) := mul_one _
    _ ≤ _ := markedMinorDirty_pending_choices H hρ₀ hρ₁

end ArtinMatthews
