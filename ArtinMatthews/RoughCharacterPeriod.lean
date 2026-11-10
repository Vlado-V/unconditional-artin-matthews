module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! Exact complete-period cancellation and bounded interval sums for actual
nonprincipal Dirichlet characters. -/
noncomputable section
namespace ArtinMatthews

open Finset
open scoped BigOperators Classical

variable {q : ℕ} [NeZero q]

theorem rough_character_residue_range_sum (f : ZMod q → ℂ) :
    (∑ n ∈ range q, f (n : ZMod q)) = ∑ z : ZMod q, f z := by
  apply Finset.sum_bij (s := range q) (t := (univ : Finset (ZMod q)))
    (f := fun n : ℕ => f (n : ZMod q)) (g := f)
    (fun (n : ℕ) _ => (n : ZMod q))
  · intro n _
    exact mem_univ _
  · intro n hn m hm hnm
    have h := congrArg ZMod.val hnm
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_range.mp hn),
      Nat.mod_eq_of_lt (mem_range.mp hm)] using h
  · intro z _
    exact ⟨z.val, mem_range.mpr (ZMod.val_lt z), ZMod.natCast_zmod_val z⟩
  · intro n _
    rfl

/-- A complete translated period has exactly zero sum. -/
theorem rough_nonprincipal_character_period_zero (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (a : ℕ) :
    (∑ n ∈ range q, χ ((a + n : ℕ) : ZMod q)) = 0 := by
  calc
    _ = ∑ z : ZMod q, χ ((a : ZMod q) + z) := by
      simpa only [Nat.cast_add] using
        rough_character_residue_range_sum (fun z => χ ((a : ZMod q) + z))
    _ = ∑ z : ZMod q, χ z := Equiv.sum_comp (Equiv.addLeft (a : ZMod q)) χ
    _ = 0 := MulChar.sum_eq_zero_of_ne_one hχ

/-- After complete periods cancel, fewer than q terms remain. -/
theorem rough_nonprincipal_character_range_norm_le (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (a N : ℕ) :
    ‖∑ n ∈ range N, χ ((a + n : ℕ) : ZMod q)‖ ≤ (q : ℝ) := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
      by_cases hN : N < q
      · calc
          _ ≤ ∑ n ∈ range N, ‖χ ((a + n : ℕ) : ZMod q)‖ := norm_sum_le _ _
          _ ≤ ∑ _n ∈ range N, (1 : ℝ) := sum_le_sum (fun n _ => χ.norm_le_one _)
          _ = (N : ℝ) := by simp
          _ ≤ (q : ℝ) := by exact_mod_cast hN.le
      · have hq : 0 < q := NeZero.pos q
        have hqN : q ≤ N := Nat.le_of_not_gt hN
        have hlt : N - q < N := Nat.sub_lt (hq.trans_le hqN) hq
        have he : N = (N - q) + q := (Nat.sub_add_cancel hqN).symm
        rw [he, sum_range_add]
        have hz : (∑ n ∈ range q, χ ((a + (N - q + n) : ℕ) : ZMod q)) = 0 := by
          simpa only [Nat.add_assoc] using
            rough_nonprincipal_character_period_zero χ hχ (a + (N - q))
        rw [hz, add_zero]
        exact ih (N - q) hlt

/-- Actual interval character cancellation, including empty natural intervals. -/
theorem rough_nonprincipal_character_Ioc_norm_le (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (M N : ℕ) :
    ‖∑ n ∈ Ioc M N, χ (n : ZMod q)‖ ≤ (q : ℝ) := by
  have he : Ioc M N = Ico (M + 1) (N + 1) := by
    ext n
    simp only [mem_Ioc, mem_Ico]
    omega
  rw [he, sum_Ico_eq_sum_range]
  simpa only [Nat.add_sub_add_right] using
    rough_nonprincipal_character_range_norm_le χ hχ (M + 1) (N - M)

end ArtinMatthews
