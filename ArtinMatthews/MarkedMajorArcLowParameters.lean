module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import ArtinMatthews.MarkedBonferroniTail
public import Mathlib.Analysis.SpecialFunctions.Log.Base
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

/-! Uniform numerical conversions for the low-frequency character estimate. -/
namespace ArtinMatthews
open Filter
open scoped Topology

 theorem marked_polynomial_le_exponential_length (K A τ P : ℝ) (hτ : 0 < τ) :
    ∀ᶠ L : ℝ in atTop, ∀ x : ℝ, Real.exp (τ*L) ≤ x → K*L^A ≤ x*L^(-P) := by
  have ht := (rpow_mul_exp_neg_rpow_tendsto (A+P) (by norm_num : (0:ℝ)<1) hτ).const_mul K
  simp only [Real.rpow_one,mul_zero] at ht
  filter_upwards [ht.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1)),
    eventually_gt_atTop (0:ℝ)] with L hsmall hL
  intro x hx
  have hpow : L^(A+P)*L^(-P)=L^A := by rw [← Real.rpow_add hL]; congr 1; ring
  have he : Real.exp (-τ*L)*Real.exp (τ*L)=1 := by rw [← Real.exp_add]; ring_nf; simp
  calc
    _ = (K*(L^(A+P)*Real.exp (-τ*L)))*(Real.exp (τ*L)*L^(-P)) := by
      calc
        _ = K*(L^(A+P)*L^(-P))*(Real.exp (-τ*L)*Real.exp (τ*L)) := by rw [hpow,he]; ring
        _ = _ := by ring
    _ ≤ 1*(Real.exp (τ*L)*L^(-P)) :=
      mul_le_mul_of_nonneg_right hsmall.le (by positivity)
    _ ≤ x*L^(-P) := by simpa using mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg hL.le _)

 theorem marked_modulus_log_admissible (a τ : ℝ) (ha : 0 ≤ a) (hτ : 0 < τ) :
    ∀ᶠ L : ℝ in atTop, ∀ q x : ℝ,
      q ≤ L^a → Real.exp (τ*L) ≤ x → q ≤ (Real.log x)^(a+1) := by
  filter_upwards [eventually_ge_atTop (max 1 (1/τ^(a+1)))] with L hL
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hτp : 0 < τ^(a+1) := Real.rpow_pos_of_pos hτ _
  have hscale : 1 ≤ τ^(a+1)*L := by
    have hh := (div_le_iff₀ hτp).mp ((le_max_right _ _).trans hL)
    nlinarith
  intro q x hq hx
  have hxp : 0 < x := (Real.exp_pos _).trans_le hx
  have hlog : τ*L ≤ Real.log x := (Real.le_log_iff_exp_le hxp).mpr hx
  calc
    _ ≤ L^a := hq
    _ ≤ τ^(a+1)*L^(a+1) := by
      rw [Real.rpow_add hLp,Real.rpow_one]
      nlinarith [Real.rpow_nonneg hLp.le a,mul_le_mul_of_nonneg_left hscale (Real.rpow_nonneg hLp.le a)]
    _ = (τ*L)^(a+1) := (Real.mul_rpow hτ.le hLp.le).symm
    _ ≤ (Real.log x)^(a+1) := Real.rpow_le_rpow (mul_nonneg hτ.le hLp.le) hlog (by linarith)

 theorem marked_conductor_correction_uniform (a η τ P : ℝ)
    (hη : 0 < η) (hτ : 0 < τ) :
    ∀ᶠ L : ℝ in atTop, ∀ (q : ℕ) [NeZero q] (x : ℝ),
      (q:ℝ) ≤ L^a → Real.exp (τ*L) ≤ x → x ≤ Real.exp (η*L) →
      (Nat.log 2 ⌊x⌋₊:ℝ)*Real.log q ≤ x*L^(-P) := by
  have h2 := ((Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hτ)).eventually
    (eventually_ge_atTop (2:ℝ)))
  filter_upwards [marked_polynomial_le_exponential_length (η/Real.log 2) (a+1) τ P hτ,
    h2,eventually_gt_atTop (0:ℝ)] with L hpoly hL2 hL
  intro q _ x hq hlo hhi
  have hx2 : 2 ≤ x := hL2.trans hlo
  have hxp : 0 < x := by linarith
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
  have hqp : (0:ℝ) < q := by linarith
  have hf : (0:ℝ) < (⌊x⌋₊:ℝ) := by
    exact_mod_cast (Nat.floor_pos.mpr (by linarith : (1:ℝ)≤x))
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn : (Nat.log 2 ⌊x⌋₊:ℝ) ≤ η*L/Real.log 2 := by
    calc
      _ ≤ Real.logb 2 (⌊x⌋₊:ℝ) := Real.natLog_le_logb _ _
      _ ≤ Real.log x/Real.log 2 := by
        rw [Real.logb]
        exact div_le_div_of_nonneg_right (Real.log_le_log hf (Nat.floor_le hxp.le)) hlog2.le
      _ ≤ _ := div_le_div_of_nonneg_right ((Real.log_le_iff_le_exp hxp).mpr hhi) hlog2.le
  have hqlog : Real.log q ≤ L^a := (Real.log_le_sub_one_of_pos hqp).trans (by linarith)
  calc
    _ ≤ (η*L/Real.log 2)*L^a := mul_le_mul hn hqlog (Real.log_nonneg hq1) (by positivity)
    _ = (η/Real.log 2)*L^(a+1) := by rw [Real.rpow_add hL,Real.rpow_one]; ring
    _ ≤ _ := hpoly x hlo

end ArtinMatthews
