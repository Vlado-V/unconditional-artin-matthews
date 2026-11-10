module

public import Mathlib.Analysis.Complex.Norm
public import ArtinMatthews.MarkedEstimateDeweighting
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

/-! The same scale-preserving Cauchy bound for arbitrary bounded complex
tests. The coefficient bound is needed only on the finite summation set. -/

namespace ArtinMatthews

open scoped BigOperators

theorem marked_deweighting_scaled_bounded {ι : Type*} (S : Finset ι)
    (w d : ι → ℝ) (a : ι → ℂ) {A B t C : ℝ}
    (hw : ∀ i ∈ S, 0 ≤ w i) (hC : 0 ≤ C) (ha : ∀ i ∈ S, ‖a i‖ ≤ C)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ht : 0 ≤ t)
    (hmass : ∑ i ∈ S, w i ≤ A * t) (hvariance : ∑ i ∈ S, w i * d i ^ 2 ≤ B * t) :
    ‖∑ i ∈ S, (w i : ℂ) * a i * (d i : ℂ)‖ ≤ C * Real.sqrt (A * B) * t := by
  have h := marked_deweighting_of_mass_bounds S w d a hw hC ha hmass hvariance
  have hs : Real.sqrt (A * t) * Real.sqrt (B * t) = Real.sqrt (A * B) * t := by
    rw [Real.sqrt_mul hA, Real.sqrt_mul hB]
    calc
      _ = (Real.sqrt A * Real.sqrt B) * (Real.sqrt t * Real.sqrt t) := by ring
      _ = _ := by rw [Real.mul_self_sqrt ht, Real.sqrt_mul hA]
  calc
    _ ≤ C * Real.sqrt (A * t) * Real.sqrt (B * t) := h
    _ = C * (Real.sqrt (A * t) * Real.sqrt (B * t)) := by ring
    _ = _ := by rw [hs]; ring

end ArtinMatthews
