module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
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

/-! The numerical discriminant bound for the actual integral Kummer basis. -/
namespace ArtinMatthews.KummerDiscriminant

theorem factorial_mul_pow_sq_le {d q : ℕ} (hq : 1 ≤ q) (hd : d ≤ q^2) :
    ((d.factorial : ℝ) * (q : ℝ)^d)^2 ≤ (q : ℝ)^(6*q^2) := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hdR : (d : ℝ) ≤ (q : ℝ)^2 := by exact_mod_cast hd
  have hf : (d.factorial : ℝ) ≤ (d : ℝ)^d := by
    exact_mod_cast Nat.factorial_le_pow d
  have hpow : (d : ℝ)^d ≤ ((q : ℝ)^2)^d :=
    pow_le_pow_left₀ (by positivity) hdR d
  calc
    _ ≤ (((q : ℝ)^2)^d * (q : ℝ)^d)^2 := by
      gcongr
      exact hf.trans hpow
    _ = (q : ℝ)^(6*d) := by
      rw [← pow_mul, ← pow_add, ← pow_mul]
      congr 1
      omega
    _ ≤ _ := pow_le_pow_right₀ hqR (Nat.mul_le_mul_left 6 hd)

theorem log_le_six_sq_log {D : ℝ} (hD : 0 < D) {q : ℕ} (hq : 0 < q)
    (hupper : D ≤ (q : ℝ)^(6*q^2)) :
    Real.log D ≤ 6*(q : ℝ)^2*Real.log q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have h := (Real.log_le_log_iff hD (pow_pos hqR _)).mpr hupper
  rw [Real.log_pow] at h
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h

end ArtinMatthews.KummerDiscriminant
