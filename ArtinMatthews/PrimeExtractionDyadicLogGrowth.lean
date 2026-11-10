module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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


set_option backward.privateInPublic true
@[expose] public section

/-! The actual natural cutoff has only a square-logarithmic dyadic cost. -/

namespace ArtinMatthews

open Filter

theorem primeExtractionDyadicLogGrowth {N : ℕ} {T x : ℝ}
    (hT : 0 ≤ T) (hx : 1 ≤ x) (hlogT : Real.log (T+1) ≤ Real.log x)
    (hlogx : 1 ≤ Real.log x) (hN : (N : ℝ) ≤ T*x) :
    1 + Real.log ((N : ℝ)+1) / Real.log 2 ≤
      (1+2/Real.log 2)*Real.log x := by
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T+1 := by linarith
  have harg : (N : ℝ)+1 ≤ (T+1)*x := by nlinarith
  have hlog : Real.log ((N : ℝ)+1) ≤ 2*Real.log x := by
    calc
      _ ≤ Real.log ((T+1)*x) := Real.log_le_log (by positivity) harg
      _ = Real.log (T+1) + Real.log x := Real.log_mul hT0.ne' hx0.ne'
      _ ≤ _ := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    _ ≤ 1 + (2*Real.log x)/Real.log 2 :=
      add_le_add_right (div_le_div_of_nonneg_right hlog hlog2.le) 1
    _ = 1+(2/Real.log 2)*Real.log x := by ring
    _ ≤ Real.log x+(2/Real.log 2)*Real.log x := by linarith only [hlogx]
    _ = _ := by ring

theorem primeExtractionDyadicMassLogGrowth {N : ℕ} {T x : ℝ}
    (hT : 0 ≤ T) (hx : 1 ≤ x) (hlogT : Real.log (T+1) ≤ Real.log x)
    (hlogx : 1 ≤ Real.log x) (hN : (N : ℝ) ≤ T*x) :
    (N : ℝ)*(1+Real.log ((N : ℝ)+1)/Real.log 2)^2 ≤
      T*(1+2/Real.log 2)^2*x*(Real.log x)^2 := by
  have hbase : 0 ≤ 1+Real.log ((N : ℝ)+1)/Real.log 2 := by
    have hlog : 0 ≤ Real.log ((N : ℝ)+1) :=
      Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
    positivity
  have hpow := pow_le_pow_left₀ hbase
    (primeExtractionDyadicLogGrowth hT hx hlogT hlogx hN) 2
  calc
    _ ≤ (T*x)*((1+2/Real.log 2)*Real.log x)^2 :=
      mul_le_mul hN hpow (sq_nonneg _) (mul_nonneg hT (by linarith))
    _ = _ := by ring

/-- The precise floor/log profile consumed by the actual Mellin error. -/
theorem primeExtractionDyadicFloorLogGrowth (T : ℝ) (hT : 0 ≤ T) :
    ∀ᶠ x : ℝ in atTop,
      (⌊T*x⌋₊ : ℝ)*(1+Real.log ((⌊T*x⌋₊ : ℝ)+1)/Real.log 2)^2 ≤
        T*(1+2/Real.log 2)^2*x*(Real.log x)^2 := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (Real.log (T+1)),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hx hlogT hlogx
  exact primeExtractionDyadicMassLogGrowth hT hx hlogT hlogx
    (Nat.floor_le (mul_nonneg hT (by linarith)))

end ArtinMatthews
