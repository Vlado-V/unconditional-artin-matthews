module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
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

/-! Literal Gamma recurrence lower bounds on a vertical line.  These
will control the actual J/I series uniformly in imaginary order. -/

noncomputable section
open scoped BigOperators

namespace ArtinMatthews

theorem spectral_Gamma_shift_norm_lower (w : ℂ) (hw : w.re = 1) (n : ℕ) :
    (n.factorial : ℝ)*‖Complex.Gamma w‖ ≤ ‖Complex.Gamma (w+n)‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hre : 0 < (w+(n : ℂ)).re := by simp only [Complex.add_re,Complex.natCast_re,hw]; positivity
    have hne : w+(n : ℂ) ≠ 0 := by intro h; rw [h,Complex.zero_re] at hre; exact lt_irrefl _ hre
    have hfactor : (n+1 : ℝ) ≤ ‖w+(n : ℂ)‖ := by
      have h := Complex.re_le_norm (w+(n : ℂ))
      simpa only [Complex.add_re,Complex.natCast_re,hw,add_comm] using h
    rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,
      Nat.cast_add,Nat.cast_one,← add_assoc,Complex.Gamma_add_one _ hne,norm_mul]
    calc
      _ = ((n : ℝ)+1)*((n.factorial : ℝ)*‖Complex.Gamma w‖) := by ring
      _ ≤ ‖w+(n : ℂ)‖*‖Complex.Gamma (w+(n : ℂ))‖ :=
        mul_le_mul hfactor ih (by positivity) (norm_nonneg _)

theorem spectral_Gamma_shift_norm_lower_base (w : ℂ) (hw : w.re = 1) (n : ℕ) :
    ‖Complex.Gamma w‖ ≤ ‖Complex.Gamma (w+n)‖ := by
  have h := spectral_Gamma_shift_norm_lower w hw n
  calc
    _ = 1*‖Complex.Gamma w‖ := by ring
    _ ≤ (n.factorial : ℝ)*‖Complex.Gamma w‖ := by
      gcongr
      exact_mod_cast Nat.factorial_pos n
    _ ≤ _ := h

end ArtinMatthews
