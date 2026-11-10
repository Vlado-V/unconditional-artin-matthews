module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import ArtinMatthews.GiantSignedCleanBudget
public import ArtinMatthews.IdealSourceCleanCounts
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The literal residual counts and coefficient budget fit the original
exponential prime lower edge, uniformly in every growing group carrier. -/
namespace ArtinMatthews
open Filter
open scoped Topology
noncomputable section

theorem giantSignedResidualBudget_eventually
    (v c E C₀ N C₁ : ℝ) (m J ell : ℕ)
    (hv : 0 < v) (hc : 0 < c) (hC₀ : 0 ≤ C₀) :
    ∀ᶠ L : ℝ in atTop, ∀ (b n : ℕ) (cost : ℝ),
      (b : ℝ) ≤ C₀ * Real.log L → (n : ℝ) ≤ L ^ N → cost ≤ L ^ C₁ →
      (n : ℝ) / Real.exp (L ^ c) < 1 ∧
      (b * (m + ell) : ℕ) * ((n : ℝ) / Real.exp (L ^ c)) ≤ (1 / 2 : ℝ) ∧
      (b * (J + ell) : ℕ) * ((n : ℝ) / Real.exp (L ^ c)) ≤ (1 / 2 : ℝ) ∧
      cost * (((b * m) * (2 * (J + ell)) : ℕ) / (v * Real.exp (L ^ c))) +
        2 * (b * (m + ell) : ℕ) * ((n : ℝ) / Real.exp (L ^ c)) * cost ≤
          L ^ (-E) / 4 := by
  let A := max (3 : ℝ) (max N C₁)
  have hA : 0 ≤ A := (by norm_num : (0 : ℝ) ≤ 3).trans (le_max_left _ _)
  have h3 : (3 : ℝ) ≤ A := le_max_left _ _
  have hN : N ≤ A := (le_max_left _ _).trans (le_max_right _ _)
  have hC₁ : C₁ ≤ A := (le_max_right _ _).trans (le_max_right _ _)
  have hbudget := Real.tendsto_exp_atTop.eventually
    (giantSignedCleanBudget_eventually v A E c hv hA hc)
  filter_upwards [hbudget, eventually_ge_atTop (1 : ℝ), eventually_ge_atTop C₀,
    eventually_ge_atTop ((m + ell : ℕ) : ℝ),
    eventually_ge_atTop ((m * (2 * (J + ell)) : ℕ) : ℝ),
    eventually_ge_atTop ((J + ell : ℕ) : ℝ)] with L hb hL hCL hf hc' hd
  simp only [Real.log_exp] at hb
  intro b n cost hgroups hn hcost
  have hpow : L ^ (3 : ℕ) ≤ L ^ A := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hL h3
  have hn' : (n : ℝ) ≤ L ^ A :=
    hn.trans (Real.rpow_le_rpow_of_exponent_le hL hN)
  have hf' : ((b * (m + ell) : ℕ) : ℝ) ≤ L ^ A :=
    (idealSource_group_count_polynomial hL hC₀ hCL hgroups hf).trans hpow
  have hc'' : (((b * m) * (2 * (J + ell)) : ℕ) : ℝ) ≤ L ^ A := by
    rw [Nat.mul_assoc]
    exact (idealSource_group_count_polynomial hL hC₀ hCL hgroups hc').trans hpow
  have hd' : ((b * (J + ell) : ℕ) : ℝ) ≤ L ^ A :=
    (idealSource_group_count_polynomial hL hC₀ hCL hgroups hd).trans hpow
  have hcost' : cost ≤ L ^ A :=
    hcost.trans (Real.rpow_le_rpow_of_exponent_le hL hC₁)
  simpa only [Real.log_exp] using
    hb (n : ℝ) ((b * (m + ell) : ℕ) : ℝ)
      (((b * m) * (2 * (J + ell)) : ℕ) : ℝ) ((b * (J + ell) : ℕ) : ℝ) cost
      (Nat.cast_nonneg _) hn' (Nat.cast_nonneg _) hf' (Nat.cast_nonneg _) hc'' hd' hcost'

end
end ArtinMatthews
