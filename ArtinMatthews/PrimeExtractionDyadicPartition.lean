module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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


set_option backward.privateInPublic true
@[expose] public section

/-! Exact dyadic partition of the finite integer extraction interval.
The fiber proof follows the genuine finite partition in
OAI.NumberTheory.TwoPoint.Fourier.MinorArcDyadicWindows. -/

namespace ArtinMatthews

open scoped BigOperators

def primeExtractionDyadicBlock (N k : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 N).filter fun n => Nat.log 2 n = k

theorem primeExtractionDyadicBlock_bounds {N k n : ℕ}
    (hn : n ∈ primeExtractionDyadicBlock N k) : 2 ^ k ≤ n ∧ n < 2 * 2 ^ k := by
  obtain ⟨hnI, hlog⟩ := Finset.mem_filter.mp hn
  have hn0 : n ≠ 0 := (Finset.mem_Ioc.mp hnI).1.ne'
  constructor
  · simpa only [hlog] using Nat.pow_log_le_self 2 hn0
  · simpa only [hlog, pow_succ'] using Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n

/-- Every fiber is literally a truncated dyadic integer interval. -/
theorem primeExtractionDyadicBlock_eq_Ico (N k : ℕ) :
    primeExtractionDyadicBlock N k = Finset.Ico (2 ^ k) (min (N + 1) (2 * 2 ^ k)) := by
  ext n
  constructor
  · intro hn
    have hb := primeExtractionDyadicBlock_bounds hn
    exact Finset.mem_Ico.mpr ⟨hb.1, lt_min
      (Nat.lt_succ_of_le (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).2) hb.2⟩
  · intro hn
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hn
    have hn0 : 0 < n := lt_of_lt_of_le (by positivity : 0 < 2 ^ k) hlo
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioc.mpr ⟨hn0, Nat.le_of_lt_succ (lt_of_lt_of_le hhi (min_le_left _ _))⟩, ?_⟩
    exact Nat.log_eq_of_pow_le_of_lt_pow hlo (by
      simpa only [pow_succ'] using lt_of_lt_of_le hhi (min_le_right _ _))

theorem primeExtractionDyadicBlock_card_le (N k : ℕ) :
    (primeExtractionDyadicBlock N k).card ≤ 2 ^ k := by
  have hsub : primeExtractionDyadicBlock N k ⊆ Finset.Ico (2 ^ k) (2 * 2 ^ k) :=
    fun n hn => Finset.mem_Ico.mpr (primeExtractionDyadicBlock_bounds hn)
  have h := Finset.card_le_card hsub
  simpa only [Nat.card_Ico, two_mul, Nat.add_sub_cancel_left] using h

theorem prime_extraction_dyadic_sum {R : Type*} [AddCommMonoid R] (N : ℕ) (f : ℕ → R) :
    (∑ n ∈ Finset.Ioc 0 N, f n) =
      ∑ k ∈ Finset.range (Nat.log 2 N + 1), ∑ n ∈ primeExtractionDyadicBlock N k, f n := by
  symm
  exact Finset.sum_fiberwise_of_maps_to (fun n hn => Finset.mem_range.mpr
    (Nat.lt_succ_of_le (Nat.log_mono_right (Finset.mem_Ioc.mp hn).2))) f

theorem prime_extraction_dyadic_double_sum {R : Type*} [AddCommMonoid R]
    (N : ℕ) (F : ℕ → ℕ → R) :
    (∑ m ∈ Finset.Ioc 0 N, ∑ n ∈ Finset.Ioc 0 N, F m n) =
      ∑ k ∈ Finset.range (Nat.log 2 N + 1), ∑ l ∈ Finset.range (Nat.log 2 N + 1),
        ∑ m ∈ primeExtractionDyadicBlock N k, ∑ n ∈ primeExtractionDyadicBlock N l, F m n := by
  classical
  calc
    _ = ∑ k ∈ Finset.range (Nat.log 2 N + 1), ∑ m ∈ primeExtractionDyadicBlock N k,
        ∑ n ∈ Finset.Ioc 0 N, F m n := prime_extraction_dyadic_sum N _
    _ = ∑ k ∈ Finset.range (Nat.log 2 N + 1), ∑ m ∈ primeExtractionDyadicBlock N k,
        ∑ l ∈ Finset.range (Nat.log 2 N + 1), ∑ n ∈ primeExtractionDyadicBlock N l, F m n := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro m _
      exact prime_extraction_dyadic_sum N _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]

theorem primeExtractionDyadicIndex_count_le (N : ℕ) :
    ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤ 1 + Real.log (N + 1) / Real.log 2 := by
  have h := (Real.natLog_le_logb (N + 1) 2)
  have hm : ((Nat.log 2 N : ℕ) : ℝ) ≤ Nat.log 2 (N + 1) :=
    Nat.cast_le.mpr (Nat.log_mono_right (Nat.le_succ N))
  simp only [Real.logb, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at h ⊢
  linarith

end ArtinMatthews
