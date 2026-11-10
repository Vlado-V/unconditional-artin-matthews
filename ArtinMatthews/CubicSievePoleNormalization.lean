module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! Exact normalization of the value, derivative, and retained errors. -/

noncomputable section
namespace ArtinMatthews

theorem cubicSieve_pole_normalized_envelope {x L W γ C E J J' : ℝ}
    (hx : 0 < x) (hL : 1 ≤ L) (hW : 0 < W) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hJ : |J| ≤ W * C * E / (γ ^ 2 * L ^ 2) + 1 / L ^ 3)
    (hJ' : |J'| ≤ W * C * E / (γ * L) + 1 / L ^ 3) :
    L / (x * W) * (2 * x * (2 * L * |J| + |J'|) + 2 * x / L ^ 2) ≤
      6 * C * E / γ ^ 2 + 8 / (W * L) := by
  have hL₀ : 0 < L := zero_lt_one.trans_le hL
  have hγsq : γ ^ 2 ≤ γ := by nlinarith only [hγ1, hγ]
  have hγterm : 2 * C * E / γ ≤ 2 * C * E / γ ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hγ) hγsq
  have hLsq : L ≤ L ^ 2 := by nlinarith only [hL]
  have hLterm : 2 / (W * L ^ 2) ≤ 2 / (W * L) :=
    div_le_div_of_nonneg_left (by norm_num) (mul_pos hW hL₀)
      (mul_le_mul_of_nonneg_left hLsq hW.le)
  calc
    _ ≤ L / (x * W) * (2 * x *
        (2 * L * (W * C * E / (γ ^ 2 * L ^ 2) + 1 / L ^ 3) +
          (W * C * E / (γ * L) + 1 / L ^ 3)) + 2 * x / L ^ 2) := by
      gcongr
    _ = 4 * C * E / γ ^ 2 + 2 * C * E / γ + 6 / (W * L) + 2 / (W * L ^ 2) := by
      field_simp
      ring
    _ ≤ 4 * C * E / γ ^ 2 + 2 * C * E / γ ^ 2 + 6 / (W * L) + 2 / (W * L) :=
      add_le_add (add_le_add (add_le_add le_rfl hγterm) le_rfl) hLterm
    _ = _ := by ring

end ArtinMatthews
