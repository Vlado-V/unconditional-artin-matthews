module

public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Algebra.Order.Floor.Semifield
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
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! Explicit floor and Euler--Mascheroni errors for the divisor hyperbola. -/

noncomputable section
namespace ArtinMatthews

theorem cubicSieve_harmonic_floor_error {y : ℝ} (hy : 1 ≤ y) :
    |(harmonic ⌊y⌋₊ : ℝ) - (Real.log y + Real.eulerMascheroniConstant)| ≤ 2 / y := by
  let n := ⌊y⌋₊
  have hy₀ : 0 < y := zero_lt_one.trans_le hy
  have hn : 0 < n := Nat.floor_pos.mpr hy
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ : (0 : ℝ) < n := zero_lt_one.trans_le hn₁
  have hfloor : (n : ℝ) ≤ y := Nat.floor_le hy₀.le
  have hceil : y ≤ (n : ℝ) + 1 := (Nat.lt_floor_add_one y).le
  have hloglo := Real.log_le_log hn₀ hfloor
  have hloghi := Real.log_le_log hy₀ hceil
  have hupper := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n
  simp only [Real.eulerMascheroniSeq] at hupper
  have hlower := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  simp only [Real.eulerMascheroniSeq', ite_eq_right hn.ne'] at hlower
  have hgap : Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) ≤ 1 / (n : ℝ) := by
    rw [← Real.log_div (by positivity) hn₀.ne']
    have h := Real.log_le_sub_one_of_pos
      (div_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1) hn₀)
    convert h using 1
    field_simp
    ring
  have hinv : 1 / (n : ℝ) ≤ 2 / y := (div_le_div_iff₀ hn₀ hy₀).mpr (by linarith)
  change |(harmonic n : ℝ) - (Real.log y + Real.eulerMascheroniConstant)| ≤ 2 / y
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem cubicSieve_harmonic_div_error {M a : ℕ} (ha : 0 < a) (haM : a ≤ M) :
    |(harmonic (M / a) : ℝ) -
      (Real.log (M : ℝ) + Real.eulerMascheroniConstant - Real.log (a : ℝ))| ≤
      2 * (a : ℝ) / M := by
  have hM : (0 : ℝ) < M := by exact_mod_cast ha.trans_le haM
  have ha₀ : (0 : ℝ) < a := by exact_mod_cast ha
  have hy : 1 ≤ (M : ℝ) / a := (le_div_iff₀ ha₀).mpr (by
    simpa only [one_mul] using (Nat.cast_le.mpr haM : (a : ℝ) ≤ M))
  have h := cubicSieve_harmonic_floor_error hy
  rw [Nat.floor_div_eq_div, Real.log_div hM.ne' ha₀.ne', div_div_eq_mul_div] at h
  convert h using 2
  ring

theorem cubicSieve_floor_div_error (M a : ℕ) :
    |((M / a : ℕ) : ℝ) - (M : ℝ) / a| ≤ 1 := by
  rw [← Nat.floor_div_eq_div (K := ℝ) M a]
  have hlow := Nat.floor_le (div_nonneg (Nat.cast_nonneg M) (Nat.cast_nonneg a) :
    0 ≤ (M : ℝ) / a)
  have hhigh := Nat.lt_floor_add_one ((M : ℝ) / a)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end ArtinMatthews
