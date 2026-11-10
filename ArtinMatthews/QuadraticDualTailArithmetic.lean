module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.QuadraticScale
noncomputable section

theorem quadraticDualTail_scale_eq {M D Q : ℝ}
    (hM : 0 < M) (hD : 0 < D) (hQ : 0 < Q) (σ : ℝ) :
    (M / D / Real.sqrt Q) * (M / D / Q) ^ (-σ) =
      M ^ (1 - σ) * D ^ (σ - 1) * Q ^ (σ - 1 / 2) := by
  rw [Real.rpow_neg (by positivity : 0 ≤ M / D / Q),
    Real.div_rpow (by positivity : 0 ≤ M / D) hQ.le, Real.div_rpow hM.le hD.le,
    Real.rpow_sub hM, Real.rpow_sub hD, Real.rpow_sub hQ,
    Real.rpow_one, Real.rpow_one, ← Real.sqrt_eq_rpow]
  field_simp (disch := positivity)

theorem quadraticDualTail_conductor_le {q Q P σ : ℝ}
    (hq : 1 ≤ q) (hQ : 0 < Q) (hP : 0 < P) (hσ : 1 ≤ σ)
    (hscale : q ^ 2 * Q ≤ 4 * P ^ 2) :
    q ^ σ * Q ^ (σ - 1 / 2) ≤ 4 ^ (σ - 1 / 2) * P ^ (2 * σ - 1) := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have ht : 0 ≤ σ - 1 / 2 := by linarith
  have hexp : σ ≤ 2 * (σ - 1 / 2) := by linarith
  calc
    _ ≤ q ^ (2 * (σ - 1 / 2)) * Q ^ (σ - 1 / 2) :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hq hexp)
        (Real.rpow_nonneg hQ.le _)
    _ = (q ^ 2 * Q) ^ (σ - 1 / 2) := by
      rw [Real.mul_rpow (sq_nonneg q) hQ.le, ← Real.rpow_two q,
        ← Real.rpow_mul hq0.le]
    _ ≤ (4 * P ^ 2) ^ (σ - 1 / 2) :=
      Real.rpow_le_rpow (mul_nonneg (sq_nonneg q) hQ.le) hscale ht
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (sq_nonneg P),
        ← Real.rpow_two P, ← Real.rpow_mul hP.le]
      congr 1
      ring

end
end ArtinMatthews.QuadraticScale
