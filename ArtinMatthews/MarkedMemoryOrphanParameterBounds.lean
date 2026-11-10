module

public import ArtinMatthews.MarkedMinorArcProductMassActual
public import ArtinMatthews.MarkedTypeIIGoodFirst
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

/-! Explicit bounds for the original moment length and slot count.
Their exponents remain 1/2 and 1/100; the harmless 1/4 upper envelope
below is used only in proving a strictly smaller than log-squared cost. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped Topology

theorem markedMemoryMomentLength_sqrt_bound {x : ℝ} (hlog : 1≤Real.log x) :
    (markedMemoryMomentLength x:ℝ)+1≤4*(Real.log x)^(1/2:ℝ) ∧
      (markedMemoryMomentLength x:ℝ)+2≤(Real.log x)^(1/2:ℝ)+4 := by
  have hL : 0≤Real.log x := by linarith
  have hs : 1≤(Real.log x)^(1/2:ℝ) := Real.one_le_rpow hlog (by norm_num)
  have hc := Nat.ceil_lt_add_one (div_nonneg (Real.rpow_nonneg hL (1/2:ℝ)) (by norm_num : (0:ℝ)≤2))
  unfold markedMemoryMomentLength
  push_cast
  constructor <;> linarith

theorem markedMemoryActiveOccurrences_rpow_bound (K : ℕ) {x : ℝ} (hlog : 1≤Real.log x) :
    (K*((markedMemoryMomentLength x+1)*markedPadSlots x):ℕ) ≤
      (8*(K:ℝ)*(Real.log x)^(3/4:ℝ)) := by
  have hL : 0<Real.log x := by linarith
  have hN := (markedMemoryMomentLength_sqrt_bound hlog).1
  have hq : 1≤(Real.log x)^(1/4:ℝ) := Real.one_le_rpow hlog (by norm_num)
  have hf := Nat.floor_le (Real.rpow_nonneg hL.le (1/100:ℝ))
  have hp : (Real.log x)^(1/100:ℝ)≤(Real.log x)^(1/4:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hlog (by norm_num)
  have hM : (markedPadSlots x:ℝ)≤2*(Real.log x)^(1/4:ℝ) := by
    unfold markedPadSlots
    push_cast
    linarith
  have hmul := mul_le_mul hN hM (Nat.cast_nonneg _) (by positivity)
  have he : (Real.log x)^(1/2:ℝ)*(Real.log x)^(1/4:ℝ)=(Real.log x)^(3/4:ℝ) := by
    rw [← Real.rpow_add hL]
    norm_num
  have hh : ((markedMemoryMomentLength x:ℝ)+1)*(markedPadSlots x:ℝ)≤
      8*(Real.log x)^(3/4:ℝ) := by nlinarith
  have hk := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg K (α := ℝ))
  push_cast
  nlinarith

theorem markedMemoryMomentLength_log_bound :
    ∀ᶠ x : ℝ in atTop,
      Real.log ((markedMemoryMomentLength x:ℝ)+2)≤(Real.log x)^(1/4:ℝ) := by
  have h1 := rpow_mul_exp_neg_rpow_tendsto (1/2:ℝ)
    (by norm_num : (0:ℝ)<1/4) (by norm_num : (0:ℝ)<1)
  have h0 := rpow_mul_exp_neg_rpow_tendsto (0:ℝ)
    (by norm_num : (0:ℝ)<1/4) (by norm_num : (0:ℝ)<1)
  have ht : Tendsto (fun L : ℝ => (L^(1/2:ℝ)+4)*Real.exp (-L^(1/4:ℝ))) atTop (nhds 0) := by
    convert h1.add (h0.const_mul 4) using 1
    · ext L
      simp only [Real.rpow_zero,one_mul,neg_mul]
      ring
    · norm_num
  filter_upwards [(ht.comp Real.tendsto_log_atTop).eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hx hlog
  have hexp : (Real.log x)^(1/2:ℝ)+4≤Real.exp ((Real.log x)^(1/4:ℝ)) := by
    have hh : ((Real.log x)^(1/2:ℝ)+4)/Real.exp ((Real.log x)^(1/4:ℝ))<1 := by
      simpa only [Function.comp_def,Real.exp_neg,div_eq_mul_inv] using hx
    simpa only [one_mul] using ((div_lt_iff₀ (Real.exp_pos _)).mp hh).le
  apply (Real.log_le_iff_le_exp (by positivity : (0:ℝ)<(markedMemoryMomentLength x:ℝ)+2)).mpr
  exact (markedMemoryMomentLength_sqrt_bound hlog).2.trans hexp

theorem markedMemoryMomentLength_sq_bound {x : ℝ} (hlog : 1≤Real.log x) :
    ((markedMemoryMomentLength x:ℝ)+1)^2≤16*Real.log x := by
  have hL : 0<Real.log x := by linarith
  have hn := (markedMemoryMomentLength_sqrt_bound hlog).1
  have hs : ((Real.log x)^(1/2:ℝ))^2=Real.log x := by
    rw [← Real.rpow_mul_natCast hL.le]
    norm_num
  nlinarith [Real.rpow_nonneg hL.le (1/2:ℝ),Nat.cast_nonneg (markedMemoryMomentLength x) (α := ℝ)]

end
end ArtinMatthews
