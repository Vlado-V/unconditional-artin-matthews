module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import ArtinMatthews.MarkedBonferroniTail
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
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! Polynomial modulus and logarithmic depth costs fit inside one extra
small-prime cutoff factor. -/
namespace ArtinMatthews
open Filter
open scoped Topology

 theorem marked_polynomial_le_exp_rpow (K a κ : ℝ) (hκ : 0 < κ) :
    ∀ᶠ L : ℝ in atTop, K*L^a ≤ Real.exp (L^κ) := by
  have ht := (rpow_mul_exp_neg_rpow_tendsto a hκ (by norm_num : (0:ℝ)<1)).const_mul K
  simp only [neg_one_mul,mul_zero] at ht
  filter_upwards [ht.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1))] with L hL
  have he : Real.exp (-(L^κ))*Real.exp (L^κ)=1 := by rw [← Real.exp_add]; simp
  calc
    _ = (K*(L^a*Real.exp (-(L^κ))))*Real.exp (L^κ) := by
      calc
        _ = K*L^a*(Real.exp (-(L^κ))*Real.exp (L^κ)) := by rw [he,mul_one]
        _ = _ := by ring
    _ ≤ 1*Real.exp (L^κ) := mul_le_mul_of_nonneg_right hL.le (Real.exp_nonneg _)
    _ = _ := one_mul _

 theorem marked_rough_count_endpoint_budget (a D κ : ℝ) (ha : 0 ≤ a)
    (hD : 0 ≤ D) (hκ : 0 < κ) :
    ∀ᶠ L : ℝ in atTop, ∀ q : ℝ, 0 ≤ q → q ≤ L^a →
      (q+2)*((⌊D*Real.log L⌋₊+1:ℕ):ℝ) ≤ Real.exp (L^κ) := by
  filter_upwards [marked_polynomial_le_exp_rpow (3*(D+1)) (a+1) κ hκ,
    eventually_ge_atTop (1:ℝ)] with L hbig hL
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hLa : 1 ≤ L^a := Real.one_le_rpow hL ha
  have hlog : Real.log L ≤ L := (Real.log_le_sub_one_of_pos hLp).trans (by linarith)
  have harg : 0 ≤ D*Real.log L := mul_nonneg hD (Real.log_nonneg hL)
  have hdepth : ((⌊D*Real.log L⌋₊+1:ℕ):ℝ) ≤ (D+1)*L := by
    simp only [Nat.cast_add,Nat.cast_one]
    have hf := Nat.floor_le harg
    have hm := mul_le_mul_of_nonneg_left hlog hD
    nlinarith
  intro q hq hqa
  calc
    _ ≤ (3*L^a)*((D+1)*L) := mul_le_mul (by linarith) hdepth (by positivity) (by positivity)
    _ = 3*(D+1)*L^(a+1) := by rw [Real.rpow_add hLp,Real.rpow_one]; ring
    _ ≤ _ := hbig

end ArtinMatthews
