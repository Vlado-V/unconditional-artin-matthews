module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
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
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open scoped BigOperators Topology

theorem sourceKPDivisibleThreeSum (r : ℂ) (N : ℕ) :
    (∑ l ∈ Finset.Icc 1 (3*N), if 3 ∣ l then r^(l/3) else 0) =
      ∑ k ∈ Finset.range N, r^(k+1) := by
  classical
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun k _ => 3*(k+1))
  · intro k hk
    simp only [Finset.mem_range] at hk
    simp only [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, dvd_mul_right 3 (k+1)⟩
  · intro a ha b hb hab
    omega
  · intro l hl
    simp only [Finset.mem_filter, Finset.mem_Icc] at hl
    obtain ⟨k, rfl⟩ := hl.2
    refine ⟨k-1, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro k hk
    simp

theorem sourceKPIntertwiningGeometric_norm {Q : ℝ} (hQ : 1 < Q) {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.exp (-6*s*(Real.log Q : ℂ))‖ < 1 := by
  rw [Complex.norm_exp, Real.exp_lt_one_iff]
  have hlog : 0 < Real.log Q := Real.log_pos hQ
  have he : (-6*s*(Real.log Q : ℂ)).re = -6*s.re*Real.log Q := by
    norm_num [Complex.mul_re]
  rw [he]
  nlinarith

theorem sourceKPIntertwiningGeometric_limit {Q : ℝ} (hQ : 1 < Q) {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto (fun N : ℕ => (1 : ℂ) +
      (1-(Q : ℂ)⁻¹) * ∑ k ∈ Finset.range N, (Complex.exp (-6*s*(Real.log Q : ℂ)))^(k+1))
      Filter.atTop (nhds ((1-(Q : ℂ)⁻¹ * Complex.exp (-6*s*(Real.log Q : ℂ))) /
        (1-Complex.exp (-6*s*(Real.log Q : ℂ))))) := by
  let r := Complex.exp (-6*s*(Real.log Q : ℂ))
  have hr : ‖r‖ < 1 := sourceKPIntertwiningGeometric_norm hQ hs
  have hr1 : 1-r ≠ 0 := by
    intro h
    rw [← sub_eq_zero.mp h, norm_one] at hr
    exact lt_irrefl _ hr
  have ht : Filter.Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, r^(k+1))
      Filter.atTop (nhds (r / (1-r))) := by
    have h := (hasSum_geometric_of_norm_lt_one hr).mul_right r
    have ht := h.tendsto_sum_nat
    simpa only [pow_succ, div_eq_mul_inv, mul_comm] using ht
  convert (ht.const_mul (1-(Q : ℂ)⁻¹)).const_add 1 using 1
  congr 1
  change (1-(Q : ℂ)⁻¹*r)/(1-r) = 1+(1-(Q : ℂ)⁻¹)*(r/(1-r))
  field_simp
  ring

end ArtinMatthews
