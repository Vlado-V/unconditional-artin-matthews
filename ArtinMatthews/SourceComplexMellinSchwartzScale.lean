module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
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

namespace ArtinMatthews.VaryingKummerAnalytic
open scoped SchwartzMap
noncomputable section

/-- A single Schwartz majorant controls all dilates with logarithmic scale at least -1. -/
theorem sourceComplexSchwartz_exp_smul_norm_le (g : 𝓢(ℂ, ℂ)) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ), -1 ≤ t → ∀ z : ℂ,
      ‖g (Real.exp t • z)‖ ≤ C * (1 + ‖z‖) ^ (-(k : ℝ)) := by
  let C₀ : ℝ := 2 ^ k *
    (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) g
  have hC₀ : 0 ≤ C₀ := by
    exact mul_nonneg (by positivity) (apply_nonneg _ _)
  refine ⟨Real.exp 1 ^ k * C₀, by positivity, ?_⟩
  intro t ht z
  have hscale : 1 ≤ Real.exp 1 * Real.exp t := by
    rw [← Real.exp_add, Real.one_le_exp_iff]
    linarith
  have hn : 1 + ‖z‖ ≤ Real.exp 1 * (1 + ‖Real.exp t • z‖) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_add, mul_one, ← mul_assoc]
    exact add_le_add (Real.one_le_exp_iff.mpr zero_le_one)
      (le_mul_of_one_le_left (norm_nonneg _) hscale)
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ‖z‖) hn k
  rw [mul_pow] at hpow
  have hf : (1 + ‖Real.exp t • z‖) ^ k * ‖g (Real.exp t • z)‖ ≤ C₀ := by
    simpa only [norm_iteratedFDeriv_zero] using
      SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) le_rfl le_rfl g
        (Real.exp t • z)
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity : 0 < (1 + ‖z‖) ^ k)).mpr
  calc
    _ = (1 + ‖z‖) ^ k * ‖g (Real.exp t • z)‖ := mul_comm _ _
    _ ≤ (Real.exp 1 ^ k * (1 + ‖Real.exp t • z‖) ^ k) * ‖g (Real.exp t • z)‖ :=
      mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
    _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hf (by positivity)

end
end ArtinMatthews.VaryingKummerAnalytic
