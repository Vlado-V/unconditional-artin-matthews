module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
noncomputable section

theorem quadraticDual_conductor_scale_bound {X M P G σ : ℝ}
    (hX : 0 < X) (hXM : X ≤ M) (hP : 0 < P) (hG : 1 ≤ G)
    (hσ : 0 ≤ σ) (hσ₁ : σ ≤ 1) :
    X ^ (1-σ/2) * (P/G) ^ (σ-1) ≤ G * M ^ (1-σ/2) * P ^ (σ-1) := by
  have hG0 := zero_lt_one.trans_le hG
  have hpow : (P/G) ^ (σ-1) = P ^ (σ-1) * G ^ (1-σ) := by
    rw [Real.div_rpow hP.le hG0.le]
    rw [show σ-1 = -(1-σ) by ring, Real.rpow_neg hG0.le, div_inv_eq_mul]
  have hGpow : G ^ (1-σ) ≤ G := by
    calc
      _ ≤ G ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hG (by linarith)
      _ = G := Real.rpow_one _
  rw [hpow]
  calc
    _ ≤ M ^ (1-σ/2) * (P ^ (σ-1) * G) := by
      apply mul_le_mul (Real.rpow_le_rpow hX.le hXM (by linarith))
        (mul_le_mul_of_nonneg_left hGpow (Real.rpow_nonneg hP.le _))
        (by positivity) (Real.rpow_nonneg (hX.le.trans hXM) _)
    _ = _ := by ring

theorem quadraticDual_divisor_scale_le {M N : ℝ} (hM : 0 ≤ M) (hN : 1 ≤ N) :
    M/N ≤ M := by
  exact div_le_self hM hN

end
end ArtinMatthews
