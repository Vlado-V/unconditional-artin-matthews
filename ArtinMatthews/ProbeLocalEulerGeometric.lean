module

public import ArtinMatthews.ProbeEulerLocalAlgebra
public import Mathlib.Analysis.Complex.Basic
public import ArtinMatthews.ProbeLocalGeometricSeries
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! Exact summation of the four support patterns in the j=0 local table.
The bridge from the literal local weights is kept separate. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open scoped BigOperators Classical
noncomputable section

def probeLocalSupportedEulerSeries (Q V W D R : ℂ) : ℂ :=
  (∑' r : ℕ, V ^ r) + (∑' k : ℕ, W ^ (k + 1)) +
    (1 - Q⁻¹) * (∑' d : ℕ, ∑' r : ℕ,
      if d < r then R ^ (d + 1) * V ^ r else 0) +
    W * (∑' d : ℕ, ∑' r : ℕ,
      if r = d + 1 then R ^ (d + 1) * V ^ r else 0) -
    D * (∑' d : ℕ, ∑' r : ℕ, if r = d then R ^ d * V ^ r else 0) -
    (Q - 1) * D * W * (∑' d : ℕ, ∑' r : ℕ,
      if d < r then R ^ d * V ^ r else 0)

theorem probeLocalSupportedEulerSeries_eq (Q V W D R : ℂ)
    (hQ : Q ≠ 0) (hV : ‖V‖ < 1) (hW : ‖W‖ < 1) (hRV : ‖R * V‖ < 1) :
    probeLocalSupportedEulerSeries Q V W D R =
      ArtinMatthews.probeGoodLocalFactor Q V W D (R * V) := by
  have hv : 1 - V ≠ 0 := by
    intro he
    have hh : V = 1 := (sub_eq_zero.mp he).symm
    rw [hh, norm_one] at hV
    exact lt_irrefl _ hV
  have hw : 1 - W ≠ 0 := by
    intro he
    have hh : W = 1 := (sub_eq_zero.mp he).symm
    rw [hh, norm_one] at hW
    exact lt_irrefl _ hW
  have he : 1 - R * V ≠ 0 := by
    intro he
    have hh : R * V = 1 := (sub_eq_zero.mp he).symm
    rw [hh, norm_one] at hRV
    exact lt_irrefl _ hRV
  have hWsum : (∑' k : ℕ, W ^ (k + 1)) = W / (1 - W) := by
    simp_rw [pow_succ]
    rw [tsum_mul_right, tsum_geometric_of_norm_lt_one hW, div_eq_mul_inv, mul_comm]
  unfold probeLocalSupportedEulerSeries
  rw [tsum_geometric_of_norm_lt_one hV, hWsum,
    probe_geometric_strict_successor_double R V hV hRV,
    probe_geometric_successor_diagonal R V hRV,
    probe_geometric_diagonal R V hRV,
    probe_geometric_strict_double R V hV hRV]
  unfold ArtinMatthews.probeGoodLocalFactor
  field_simp
  ring

end

end ArtinMatthews.VaryingKummerAnalytic
