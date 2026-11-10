module

public import ArtinMatthews.GiantSignedCleanErrorLimit
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Polynomially bounded source counts and coefficient budgets are
uniformly absorbed by the actual exponential prime lower bound. -/
namespace ArtinMatthews
open Filter
open scoped Topology
noncomputable section

theorem giantSignedCleanErrorBudget_le
    (v H Q n fresh comparisons cost : ℝ)
    (hv : 0 < v) (hH : 1 ≤ H) (hQ : 0 < Q)
    (hn0 : 0 ≤ n) (hn : n ≤ H) (hf0 : 0 ≤ fresh) (hf : fresh ≤ H)
    (hc0 : 0 ≤ comparisons) (hc : comparisons ≤ H)
    (hb : cost ≤ H) :
    cost * (comparisons / (v * Q)) + 2 * fresh * (n / Q) * cost ≤
      (v⁻¹ + 2) * H ^ 3 / Q := by
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hbc : cost * comparisons ≤ H ^ 3 := by
    calc
      _ ≤ H * H := mul_le_mul hb hc hc0 hH0
      _ ≤ H ^ 3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hH) (sq_nonneg H)]
  have hbnf : cost * fresh * n ≤ H ^ 3 := by
    calc
      _ ≤ H * fresh * n := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hb hf0) hn0
      _ ≤ H * H * n := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hf hH0) hn0
      _ ≤ H * H * H := mul_le_mul_of_nonneg_left hn (mul_nonneg hH0 hH0)
      _ = _ := by ring
  calc
    _ = (cost * comparisons / v + 2 * (cost * fresh * n)) / Q := by
      field_simp [hv.ne', hQ.ne']
    _ ≤ (H ^ 3 / v + 2 * H ^ 3) / Q := by
      apply div_le_div_of_nonneg_right _ hQ.le
      exact add_le_add (div_le_div_of_nonneg_right hbc hv.le)
        (mul_le_mul_of_nonneg_left hbnf (by norm_num))
    _ = _ := by rw [inv_eq_one_div]; ring

theorem giantSignedCleanBudget_eventually
    (v A E a : ℝ) (hv : 0 < v) (hA : 0 ≤ A) (ha : 0 < a) :
    ∀ᶠ x : ℝ in atTop,
      let H := (Real.log x) ^ A
      let Q := Real.exp ((Real.log x) ^ a)
      ∀ n fresh comparisons dim cost : ℝ,
        0 ≤ n → n ≤ H → 0 ≤ fresh → fresh ≤ H →
        0 ≤ comparisons → comparisons ≤ H → dim ≤ H →
        cost ≤ H →
        n / Q < 1 ∧ fresh * (n / Q) ≤ 1 / 2 ∧ dim * (n / Q) ≤ 1 / 2 ∧
        cost * (comparisons / (v * Q)) + 2 * fresh * (n / Q) * cost ≤
          (Real.log x) ^ (-E) / 4 := by
  have htwo := giantSignedLogErrorEnvelope_eventually_le 1 (2 * A) 0 a (1 / 2) ha (by norm_num)
  have hthree := giantSignedLogErrorEnvelope_eventually_le (v⁻¹ + 2) (3 * A) E a (1 / 4) ha (by norm_num)
  filter_upwards [htwo, hthree, Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))]
    with x hx2 hx3 hxL
  dsimp only
  intro n fresh comparisons dim cost hn0 hn hf0 hf hc0 hc hd hb
  let H := (Real.log x) ^ A
  let Q := Real.exp ((Real.log x) ^ a)
  have hL : 0 < Real.log x := zero_lt_one.trans_le hxL
  have hH : 1 ≤ H := Real.one_le_rpow hxL hA
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hQ : 0 < Q := Real.exp_pos _
  have hpow2 : H ^ 2 = (Real.log x) ^ (2 * A) := by
    dsimp only [H]
    rw [← Real.rpow_mul_natCast hL.le]
    congr 1
    norm_num
    ring
  have hpow3 : H ^ 3 = (Real.log x) ^ (3 * A) := by
    dsimp only [H]
    rw [← Real.rpow_mul_natCast hL.le]
    congr 1
    norm_num
    ring
  have hsmall : H ^ 2 / Q ≤ 1 / 2 := by
    simpa only [giantSignedLogErrorEnvelope, H, Q, hpow2, one_mul, neg_zero,
      Real.rpow_zero, mul_one] using hx2
  have herr : (v⁻¹ + 2) * H ^ 3 / Q ≤ (Real.log x) ^ (-E) / 4 := by
    have hh := hx3
    rw [giantSignedLogErrorEnvelope, ← hpow3] at hh
    change (v⁻¹ + 2) * H ^ 3 / Q ≤ _ at hh
    linarith
  have hnQ : n / Q ≤ H ^ 2 / Q := by
    apply div_le_div_of_nonneg_right _ hQ.le
    exact hn.trans (by nlinarith [mul_nonneg hH0 (sub_nonneg.mpr hH)])
  have hfn : fresh * (n / Q) ≤ H ^ 2 / Q := by
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hQ.le
    calc
      fresh * n ≤ H * H := mul_le_mul hf hn hn0 hH0
      _ = _ := by ring
  have hdn : dim * (n / Q) ≤ H ^ 2 / Q := by
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hQ.le
    calc
      dim * n ≤ H * H := mul_le_mul hd hn hn0 hH0
      _ = _ := by ring
  exact ⟨hnQ.trans_lt (hsmall.trans_lt (by norm_num)), hfn.trans hsmall, hdn.trans hsmall,
    (giantSignedCleanErrorBudget_le v H Q n fresh comparisons cost hv hH hQ hn0 hn
      hf0 hf hc0 hc hb).trans herr⟩

end
end ArtinMatthews
