module

public import ArtinMatthews.GiantCandidateSquareFiber
public import ArtinMatthews.MarkedBonferroniTail
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.NumberTheory.Chebyshev
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


set_option backward.privateInPublic true
@[expose] public section

/-! The actual exceptional ordered-fiber mass absorbs every fixed log
power. The positive-power decay comes from the candidate lower endpoint. -/
namespace ArtinMatthews
open Filter
open scoped Topology
noncomputable section

theorem giantCandidateSquareFiberMass_actual_le :
    ∀ᶠ x : ℝ in atTop,∀ X j : ℕ,
      giantCandidateSquareFiberMass (giantCandidateFullPrimes x) X j ≤
        2*(X:ℝ)*Real.exp (-(1/2)*(Real.log x)^(28/100:ℝ)) *
          Real.sqrt ((1+Real.log (X:ℝ))^(j*j)) := by
  filter_upwards [giantCandidateSquareExceptions_actual_card_eventually] with x hx
  intro X j
  have h4 : Real.sqrt (4:ℝ) = 2 := by norm_num
  have he : Real.sqrt (Real.exp (-(Real.log x)^(28/100:ℝ))) =
      Real.exp (-(1/2)*(Real.log x)^(28/100:ℝ)) := by
    rw [Real.sqrt_eq_rpow,← Real.exp_mul]
    congr 1
    ring
  calc
    _ ≤ Real.sqrt (4*(X:ℝ)*Real.exp (-(Real.log x)^(28/100:ℝ))) *
        Real.sqrt ((X:ℝ)*(1+Real.log (X:ℝ))^(j*j)) :=
      (giantCandidateSquareFiberMass_le _ X j).trans
        (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (hx X)) (Real.sqrt_nonneg _))
    _ = _ := by
      rw [Real.sqrt_mul (show 0 ≤ 4*(X:ℝ) by positivity),
        Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4),Real.sqrt_mul (Nat.cast_nonneg X),h4,he]
      calc
        _ = 2*(Real.sqrt (X:ℝ)*Real.sqrt (X:ℝ))*
            Real.exp (-(1/2)*(Real.log x)^(28/100:ℝ)) *
              Real.sqrt ((1+Real.log (X:ℝ))^(j*j)) := by ring
        _ = _ := by rw [Real.mul_self_sqrt (Nat.cast_nonneg X)]

theorem giantCandidateSquareFiberMass_log_saving (j : ℕ) (T C c A : ℝ)
    (hT : 0 ≤ T) (hC : 0 ≤ C) :
    ∀ᶠ x : ℝ in atTop, ∀ X : ℕ, (X:ℝ) ≤ T*x →
      (C*(Real.log x)^c)*giantCandidateSquareFiberMass (giantCandidateFullPrimes x) X j ≤
        x*(Real.log x)^(-A) := by
  let k := j*j
  let K := 2*C*T*(3:ℝ)^k
  have hdecay := ((rpow_mul_exp_neg_rpow_tendsto (c+(k:ℝ)+A)
    (by norm_num : (0:ℝ) < 28/100) (by norm_num : (0:ℝ) < 1/2)).comp
      Real.tendsto_log_atTop).const_mul K
  simp only [Function.comp_def,mul_zero] at hdecay
  filter_upwards [hdecay.eventually (Iio_mem_nhds (zero_lt_one : (0:ℝ)<1)),
    giantCandidateSquareFiberMass_actual_le,eventually_ge_atTop T,
    eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hs hmass hxT hx hL
  intro X hX
  let L := Real.log x
  have hL0 : 0 < L := Real.log_pos hx
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hlogX : 1+Real.log (X:ℝ) ≤ 3*L := by
    by_cases h : X=0
    · subst X
      simp only [Nat.cast_zero,Real.log_zero,add_zero]
      linarith
    · have hXp : 0 < (X:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero h)
      have hX2 : (X:ℝ) ≤ x*x := hX.trans (mul_le_mul_of_nonneg_right hxT hx0.le)
      have hlog := Real.log_le_log hXp hX2
      rw [Real.log_mul hx0.ne' hx0.ne'] at hlog
      linarith
  have hbase : 1 ≤ 1+Real.log (X:ℝ) := by
    linarith only [Real.log_natCast_nonneg X]
  have hpow : Real.sqrt ((1+Real.log (X:ℝ))^k) ≤ (3*L)^k := by
    exact (Real.sqrt_le_self_iff.mpr (Or.inr (one_le_pow₀ hbase))).trans
      (pow_le_pow_left₀ (zero_le_one.trans hbase) hlogX k)
  have hscal : 0 ≤ C*L^c := mul_nonneg hC (Real.rpow_nonneg hL0.le _)
  have hh : L^(c+(k:ℝ)+A)*L^(-A) = L^(c+(k:ℝ)) := by
    rw [← Real.rpow_add hL0]
    congr 1
    ring
  change (C*L^c)*giantCandidateSquareFiberMass (giantCandidateFullPrimes x) X j ≤ x*L^(-A)
  calc
    _ ≤ (C*L^c)*(2*(X:ℝ)*Real.exp (-(1/2)*L^(28/100:ℝ)) *
        Real.sqrt ((1+Real.log (X:ℝ))^k)) := mul_le_mul_of_nonneg_left (hmass X j) hscal
    _ ≤ (C*L^c)*(2*(T*x)*Real.exp (-(1/2)*L^(28/100:ℝ)) * (3*L)^k) := by
      apply mul_le_mul_of_nonneg_left _ hscal
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hX (by norm_num)) (Real.exp_nonneg _)) hpow
        (Real.sqrt_nonneg _) (by positivity)
    _ = (K*(L^(c+(k:ℝ)+A)*Real.exp (-(1/2)*L^(28/100:ℝ))))*(x*L^(-A)) := by
      rw [mul_pow,← Real.rpow_natCast L k]
      unfold K
      calc
        _ = (2*C*T*3^k)*x*(L^c*L^(k:ℝ))*Real.exp (-(1/2)*L^(28/100:ℝ)) := by ring
        _ = _ := by
          rw [← Real.rpow_add hL0,← hh]
          ring
    _ ≤ _ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hs.le (by positivity : 0 ≤ x*L^(-A))

end
end ArtinMatthews
