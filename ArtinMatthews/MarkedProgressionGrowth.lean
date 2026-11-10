module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
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

/-! Subpolynomial growth of the retained marking-divisor expansion.
For `k = floor ((log x)^δ)` and `z = exp (2 (log x)^β)`, the common
coefficient-mass/level envelope `(k+1) z^(k+K)` is at most `x^ε` eventually
whenever `δ,β>0` and `δ+β<1`. No growth estimate is assumed. -/

namespace ArtinMatthews

open Filter
open scoped Topology

/-- Any fixed exponential of a sublinear logarithmic power is eventually
smaller than any prescribed positive power. The coefficient `C` is arbitrary. -/
theorem marked_sublinear_log_exp_le_rpow_eventually (a C ε : ℝ)
    (ha : a < 1) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, Real.exp (C * (Real.log x) ^ a) ≤ x ^ ε := by
  have hlim0 : Tendsto (fun x : ℝ => (Real.log x) ^ (a - 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_sub] using
      (tendsto_rpow_neg_atTop (sub_pos.mpr ha)).comp Real.tendsto_log_atTop
  have hlim : Tendsto (fun x : ℝ => C * (Real.log x) ^ (a - 1)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hlim0.const_mul C
  filter_upwards [hlim.eventually (gt_mem_nhds hε), eventually_gt_atTop (1 : ℝ)] with x hx hx1
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx1
  have hpow : (Real.log x) ^ a = (Real.log x) ^ (a - 1) * Real.log x := by
    conv_lhs => rw [show a = (a - 1) + 1 by ring]
    rw [Real.rpow_add hlog, Real.rpow_one]
  rw [Real.rpow_def_of_pos hx0]
  apply Real.exp_le_exp.mpr
  rw [hpow]
  nlinarith

/-- A finite, explicit envelope for the floor-truncated divisor mass. -/
theorem marked_floor_truncation_exp_bound (t δ β : ℝ) (K : ℕ)
    (ht : 1 ≤ t) (hδ : 0 ≤ δ) (hβ : 0 ≤ β) :
    ((⌊t ^ δ⌋₊ + 1 : ℕ) : ℝ) *
        Real.exp (2 * ((⌊t ^ δ⌋₊ + K : ℕ) : ℝ) * t ^ β) ≤
      Real.exp ((3 + 2 * (K : ℝ)) * t ^ (δ + β)) := by
  let k : ℕ := ⌊t ^ δ⌋₊
  have ht0 : 0 < t := by linarith
  have hk : (k : ℝ) ≤ t ^ δ := Nat.floor_le (Real.rpow_nonneg ht0.le δ)
  have hlead : ((k + 1 : ℕ) : ℝ) ≤ Real.exp (k : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using Real.add_one_le_exp (k : ℝ)
  have hβ0 : 0 ≤ t ^ β := Real.rpow_nonneg ht0.le β
  have hδa : t ^ δ ≤ t ^ (δ + β) :=
    Real.rpow_le_rpow_of_exponent_le ht (by linarith)
  have hβa : t ^ β ≤ t ^ (δ + β) :=
    Real.rpow_le_rpow_of_exponent_le ht (by linarith)
  have hprod : t ^ (δ + β) = t ^ δ * t ^ β := Real.rpow_add ht0 δ β
  have hkprod : (k : ℝ) * t ^ β ≤ t ^ δ * t ^ β :=
    mul_le_mul_of_nonneg_right hk hβ0
  have hKprod : (K : ℝ) * t ^ β ≤ (K : ℝ) * t ^ (δ + β) :=
    mul_le_mul_of_nonneg_left hβa (Nat.cast_nonneg K)
  have hexponent : (k : ℝ) + 2 * ((k + K : ℕ) : ℝ) * t ^ β ≤
      (3 + 2 * (K : ℝ)) * t ^ (δ + β) := by
    push_cast
    nlinarith
  change ((k + 1 : ℕ) : ℝ) * Real.exp (2 * ((k + K : ℕ) : ℝ) * t ^ β) ≤ _
  calc
    _ ≤ Real.exp (k : ℝ) * Real.exp (2 * ((k + K : ℕ) : ℝ) * t ^ β) :=
      mul_le_mul_of_nonneg_right hlead (Real.exp_pos _).le
    _ = Real.exp ((k : ℝ) + 2 * ((k + K : ℕ) : ℝ) * t ^ β) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hexponent

/-- The exact retained coefficient-mass and divisor-level envelope is
`x^o(1)`, expressed without asymptotic shorthand. -/
theorem marked_truncation_mass_le_rpow_eventually (δ β : ℝ) (K : ℕ) (ε : ℝ)
    (hδ : 0 < δ) (hβ : 0 < β) (hsum : δ + β < 1) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      ((⌊(Real.log x) ^ δ⌋₊ + 1 : ℕ) : ℝ) *
          Real.exp (2 * ((⌊(Real.log x) ^ δ⌋₊ + K : ℕ) : ℝ) * (Real.log x) ^ β) ≤
        x ^ ε := by
  filter_upwards [marked_sublinear_log_exp_le_rpow_eventually (δ + β)
      (3 + 2 * (K : ℝ)) ε hsum hε,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with x hx hlog
  exact (marked_floor_truncation_exp_bound (Real.log x) δ β K hlog hδ.le hβ.le).trans hx

/-- The same bound written with the actual band-size base
`z = exp (2 (log x)^β)` and its natural-number exponent. -/
theorem marked_truncation_power_le_rpow_eventually (δ β : ℝ) (K : ℕ) (ε : ℝ)
    (hδ : 0 < δ) (hβ : 0 < β) (hsum : δ + β < 1) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      ((⌊(Real.log x) ^ δ⌋₊ + 1 : ℕ) : ℝ) *
          (Real.exp (2 * (Real.log x) ^ β)) ^ (⌊(Real.log x) ^ δ⌋₊ + K) ≤
        x ^ ε := by
  filter_upwards [marked_truncation_mass_le_rpow_eventually δ β K ε hδ hβ hsum hε]
    with x hx
  convert hx using 1
  congr 1
  rw [← Real.exp_nat_mul]
  congr 1
  ring

end ArtinMatthews
