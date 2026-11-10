module

public import ArtinMatthews.GiantPrimeSlotTelescoping
public import ArtinMatthews.MarkedMajorArcRoughMertens
public import ArtinMatthews.MarkedMajorTypeIICoefficients
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual ordinary slot weights on the positive-power threshold. The
rough proxy is eventually bounded by one on its full support. -/

namespace ArtinMatthews
noncomputable section
open Filter Finset

def giantCenteredSlotCoefficient (W z : ℝ) (m : ℕ) : ℂ :=
  if z < (m:ℝ) then markedMajorCenteredCoefficient W 0 m else 0

theorem giant_prime_slot_norm_le_one (z : ℝ) (m : ℕ) :
    ‖giantPrimeSlotCoefficient z m‖ ≤ 1 := by
  classical
  unfold giantPrimeSlotCoefficient
  split_ifs <;> simp

theorem giant_rough_slot_norm_le_one_eventually (γ : ℝ) (hγ : 0 < γ) :
    ∀ᶠ x : ℝ in atTop, ∀ m : ℕ,
      ‖giantRoughSlotCoefficient (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) m‖ ≤ 1 := by
  let E := Real.exp (Real.eulerMascheroniConstant+1)
  have hgrowth := (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 19/25)).comp Real.tendsto_log_atTop
  filter_upwards [Real.tendsto_log_atTop.eventually (marked_rough_density_inverse_cutoff (6/25) (by norm_num)),
    hgrowth.eventually (eventually_ge_atTop (E/γ)),eventually_gt_atTop (1:ℝ)] with x hV hg hx
  let L := Real.log x
  let W := Real.exp (L^(6/25:ℝ))
  have hL : 0 < L := Real.log_pos hx
  have hx₀ : 0 < x := zero_lt_one.trans hx
  have hs : x^γ = Real.exp (γ*L) := by rw [Real.rpow_def_of_pos hx₀,mul_comm]
  change E/γ ≤ L^(19/25:ℝ) at hg
  have hscale : E*L^(6/25:ℝ) ≤ γ*L := by
    calc
      _ ≤ (L^(19/25:ℝ)*γ)*L^(6/25:ℝ) :=
        mul_le_mul_of_nonneg_right ((div_le_iff₀ hγ).mp hg) (Real.rpow_nonneg hL.le _)
      _ = _ := by
        rw [mul_comm (L^(19/25:ℝ)) γ,mul_assoc,← Real.rpow_add hL]
        norm_num
  intro m
  change ‖giantRoughSlotCoefficient W (x^γ) m‖ ≤ 1
  by_cases hm : x^γ < (m:ℝ)
  · have hm₀ : 0 < (m:ℝ) := (Real.rpow_pos_of_pos hx₀ _).trans hm
    have hmL : γ*L ≤ Real.log (m:ℝ) := (Real.le_log_iff_exp_le hm₀).mpr (hs ▸ hm.le)
    have hlogm : 0 < Real.log (m:ℝ) := (mul_pos hγ hL).trans_le hmL
    have hV₀ : 0 < markedSieveEulerProduct W := markedSieveEulerProduct_pos W
    by_cases hr : ∀ p ∈ Nat.primesLE ⌊W⌋₊, ¬p ∣ m
    · have hcoef : giantRoughSlotCoefficient W (x^γ) m =
          (markedSieveEulerProduct W:ℂ)⁻¹ * ((Real.log m)⁻¹:ℝ) := by
        unfold giantRoughSlotCoefficient
        rw [ite_eq_left hm,ite_eq_left hr,mul_one]
      have hnormV : ‖(markedSieveEulerProduct W:ℂ)‖ = markedSieveEulerProduct W := by
        rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hV₀]
      have hnormLog : ‖(((Real.log m)⁻¹:ℝ):ℂ)‖ = (Real.log m)⁻¹ := by
        rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hlogm)]
      rw [hcoef,norm_mul,norm_inv,hnormV,hnormLog,← div_eq_mul_inv]
      exact (div_le_one hlogm).mpr (hV.trans (hscale.trans hmL))
    · simp [giantRoughSlotCoefficient,hm,hr]
  · simp [giantRoughSlotCoefficient,hm]

theorem giant_centered_slot_norm_bound_eventually (γ : ℝ) (hγ : 0 < γ) :
    ∀ᶠ x : ℝ in atTop, ∀ m : ℕ,
      ‖giantCenteredSlotCoefficient (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) m‖ ≤ (Real.log x)^2 := by
  filter_upwards [Real.tendsto_log_atTop.eventually (markedMajorTypeII_alpha_bound γ hγ),
    eventually_gt_atTop (0:ℝ)] with x hα hx
  intro m
  unfold giantCenteredSlotCoefficient
  by_cases hm : x^γ < (m:ℝ)
  · rw [ite_eq_left hm]
    have hs : Real.exp (γ*Real.log x)=x^γ := by rw [Real.rpow_def_of_pos hx,mul_comm]
    exact hα m 0 (hs.symm ▸ hm.le)
  · rw [ite_eq_right hm,norm_zero]
    positivity

end
end ArtinMatthews
