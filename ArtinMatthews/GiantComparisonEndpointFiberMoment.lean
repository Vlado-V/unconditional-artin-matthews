module

public import ArtinMatthews.GiantOrderedProductTuples
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import ArtinMatthews.GiantOrderedProductCount
public import ArtinMatthews.GiantOrderedProductMoment
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
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


set_option backward.privateInPublic true
@[expose] public section

/-! Iteration of the checked factor-matrix injection gives the higher
fixed moments needed for simultaneous endpoint norms. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section

theorem giant_ordered_product_fiber_pow_two_le (j n d : ℕ) :
    (giantOrderedProductFiber j n).card^(2^d:ℕ) ≤
      (giantOrderedProductFiber (j^(2^d:ℕ)) n).card := by
  induction d with
  | zero =>
    have h : (j^(2^0:ℕ)) = j := by norm_num
    rw [congrArg (fun r : ℕ => (giantOrderedProductFiber r n).card) h]
    norm_num
  | succ d ih =>
    rw [pow_succ (2:ℕ) d,pow_mul,pow_mul]
    apply (Nat.pow_le_pow_left ih 2).trans
    rw [pow_two (j^(2^d:ℕ))]
    exact giant_ordered_product_fiber_square_le (j^(2^d:ℕ)) n

theorem giant_ordered_product_fiber_pow_two_moment (j d N : ℕ) :
    (∑ n ∈ Ioc 0 N, ((giantOrderedProductFiber j n).card:ℝ)^(2^d:ℕ)) ≤
      (N:ℝ)*(1+Real.log ((N:ℝ)+1))^(j^(2^d:ℕ)) := by
  have hlog : Real.log (N:ℝ) ≤ Real.log ((N:ℝ)+1) := by
    by_cases hn : N=0
    · simp [hn]
    · exact Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) (by linarith)
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, ((giantOrderedProductFiber (j^(2^d:ℕ)) n).card:ℝ) := by
      apply sum_le_sum
      intro n _
      exact_mod_cast giant_ordered_product_fiber_pow_two_le j n d
    _ = _ := giant_ordered_product_fiber_card_sum _ _
    _ ≤ (N:ℝ)*(1+Real.log (N:ℝ))^(j^(2^d:ℕ)) := giant_ordered_product_count_le _ _
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact pow_le_pow_left₀ (add_nonneg zero_le_one (Real.log_natCast_nonneg N))
        (add_le_add le_rfl hlog) _

end
end ArtinMatthews
