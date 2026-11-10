module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.NumberTheory.AbelSummation
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

/-! Smooth summation against an explicit differentiable prefix main term. -/

noncomputable section
namespace ArtinMatthews

open Finset MeasureTheory
open scoped BigOperators

theorem cubicSieve_smooth_prefix_error (c : ℕ → ℝ) (f G g : ℝ → ℝ)
    {a b E : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hf : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hdf : ContinuousOn (deriv f) (Set.Icc a b)) (hfa : f a = 0) (hfb : f b = 0)
    (hG : ∀ t ∈ Set.Icc a b, HasDerivAt G (g t) t) (hg : ContinuousOn g (Set.Icc a b))
    (hprefix : ∀ t ∈ Set.Ioc a b, |(∑ n ∈ Icc 0 ⌊t⌋₊, c n) - G t| ≤ E) :
    |(∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f n * c n) - ∫ t in Set.Ioc a b, f t * g t| ≤
      E * ∫ t in Set.Ioc a b, |deriv f t| := by
  let P (t : ℝ) := ∑ n ∈ Icc 0 ⌊t⌋₊, c n
  have hfi : IntegrableOn (deriv f) (Set.Icc a b) := hdf.integrableOn_Icc
  have hsum : (∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f n * c n) =
      -(∫ t in Set.Ioc a b, deriv f t * P t) := by
    simpa only [hfa, hfb, zero_mul, sub_self, zero_sub] using
      sum_mul_eq_sub_sub_integral_mul (c := c) ha hab hf hfi
  have hG' : ∀ t ∈ Set.uIcc a b, HasDerivAt G (g t) t := by
    simpa only [Set.uIcc_of_le hab] using hG
  have hf' : ∀ t ∈ Set.uIcc a b, HasDerivAt f (deriv f t) t := by
    rw [Set.uIcc_of_le hab]
    exact fun t ht => (hf t ht).hasDerivAt
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul hG' hf'
    (hg.intervalIntegrable_of_Icc hab) (hdf.intervalIntegrable_of_Icc hab)
  simp only [hfa, hfb, mul_zero, sub_self, zero_sub] at hIBP
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab] at hIBP
  have hmodel : (∫ t in Set.Ioc a b, deriv f t * G t) = -(∫ t in Set.Ioc a b, f t * g t) := by
    simpa only [mul_comm] using hIBP
  have hP : IntegrableOn (fun t => deriv f t * P t) (Set.Ioc a b) :=
    (integrableOn_mul_sum_Icc c ha hfi).mono_set Set.Ioc_subset_Icc_self
  have hC : ContinuousOn G (Set.Icc a b) :=
    fun t ht => (hG t ht).continuousAt.continuousWithinAt
  have hF : IntegrableOn (fun t => deriv f t * G t) (Set.Ioc a b) :=
    (hdf.mul hC).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have herr : (∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f n * c n) - (∫ t in Set.Ioc a b, f t * g t) =
      -(∫ t in Set.Ioc a b, deriv f t * (P t - G t)) := by
    rw [hsum]
    simp_rw [mul_sub]
    rw [integral_sub hP hF, hmodel]
    ring
  rw [herr, abs_neg]
  have hbound : IntegrableOn (fun t => E * |deriv f t|) (Set.Ioc a b) :=
    (hdf.abs.const_mul E).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hb := norm_integral_le_of_norm_le
    (f := fun t => deriv f t * (P t - G t)) hbound (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [Real.norm_eq_abs, abs_mul, mul_comm (|deriv f t|)]
      exact mul_le_mul_of_nonneg_right (hprefix t ht) (abs_nonneg _))
  simpa only [Real.norm_eq_abs, integral_const_mul] using hb

end ArtinMatthews
