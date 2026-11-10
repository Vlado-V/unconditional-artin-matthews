module

public import ArtinMatthews.VaryingKummerAnalyticZeroSeparation
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Quantitative separation of the actual zeros of an entire function.
The hypotheses are explicit analytic properties; no number-field signature
is required. This generalizes the argument used in OpenAI PrimePackets'
totally-real Dedekind specialization. -/
namespace OAI.PrimeDegreePackets.AnalyticGrowth

open ArtinMatthews.ReusedGrowth
open Complex
open scoped Topology ComplexConjugate

theorem separatedZeroPole_tsum_bound {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) (hg : HasSubquadraticGrowth f)
    (hfe : ∀ z, f (1-z) = f z) (hstrip : ∀ ρ, f ρ = 0 → ρ.re ≤ 1)
    {L h B : ℝ} (hL : 0 < L) (hh : 0 < h) (hh4 : h ≤ 4/L)
    (hbase : (logDeriv f ((1+1/L : ℝ) : ℂ)).re ≤ B) :
    0 ≤ ∑' ρ, separatedZeroPole f L (1+h) ρ ∧
      (∑' ρ, separatedZeroPole f L (1+h) ρ) ≤ 676*B := by
  have hs : 1 < 1+h := by linarith
  have hs₀ : 1 < 1+1/L := by have hi := one_div_pos.mpr hL; linarith
  have Hs := hasSum_realZeroPole hf h0 hg hfe hstrip hs
  have H₀ := hasSum_realZeroPole hf h0 hg hfe hstrip hs₀
  have Hn (ρ : ℂ) : 0 ≤ separatedZeroPole f L (1+h) ρ := by
    unfold separatedZeroPole
    split
    · exact le_rfl
    · exact realZeroPole_nonneg hf h0 hstrip hs ρ
  have Hpoint (ρ : ℂ) : separatedZeroPole f L (1+h) ρ ≤
      676*realZeroPole f (1+1/L) ρ := by
    unfold separatedZeroPole
    split
    · exact mul_nonneg (by norm_num) (realZeroPole_nonneg hf h0 hstrip hs₀ ρ)
    · exact realZeroPole_le_base_of_outside_box hf h0 hstrip hL hh hh4 ρ ‹_›
  refine ⟨tsum_nonneg Hn, ?_⟩
  have H := (separatedZeroPole_summable Hs.summable).tsum_le_tsum Hpoint
    (H₀.summable.mul_left 676)
  rw [tsum_mul_left, H₀.tsum_eq] at H
  exact H.trans (mul_le_mul_of_nonneg_left hbase (by norm_num))

theorem logDeriv_re_sub_nearOneZeroPole {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) (hg : HasSubquadraticGrowth f)
    (hfe : ∀ z, f (1-z) = f z) (hstrip : ∀ ρ, f ρ = 0 → ρ.re ≤ 1)
    (L : ℝ) {s : ℝ} (hs : 1 < s) :
    (logDeriv f (s : ℂ)).re - (∑' ρ, nearOneZeroPole f L s ρ) =
      ∑' ρ, separatedZeroPole f L s ρ := by
  have H := hasSum_realZeroPole hf h0 hg hfe hstrip hs
  have Hsplit := (nearOneZeroPole_summable (L := L) H.summable).tsum_add
    (separatedZeroPole_summable (L := L) H.summable)
  simp only [zeroPole_split] at Hsplit
  rw [H.tsum_eq] at Hsplit
  linarith

theorem logDeriv_re_nearOne_error_le {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) (hg : HasSubquadraticGrowth f)
    (hfe : ∀ z, f (1-z) = f z) (hstrip : ∀ ρ, f ρ = 0 → ρ.re ≤ 1)
    {L h B : ℝ} (hL : 0 < L) (hh : 0 < h) (hh4 : h ≤ 4/L)
    (hbase : (logDeriv f ((1+1/L : ℝ) : ℂ)).re ≤ B) :
    |(logDeriv f ((1+h : ℝ) : ℂ)).re -
      (∑' ρ, nearOneZeroPole f L (1+h) ρ)| ≤ 676*B := by
  have H := separatedZeroPole_tsum_bound hf h0 hg hfe hstrip hL hh hh4 hbase
  rw [logDeriv_re_sub_nearOneZeroPole hf h0 hg hfe hstrip L (by linarith),
    abs_of_nonneg H.1]
  exact H.2

theorem logDeriv_re_error_le_of_no_near_zero {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) (hg : HasSubquadraticGrowth f)
    (hfe : ∀ z, f (1-z) = f z) (hstrip : ∀ ρ, f ρ = 0 → ρ.re ≤ 1)
    {L h B : ℝ} (hL : 0 < L) (hh : 0 < h) (hh4 : h ≤ 4/L)
    (hbase : (logDeriv f ((1+1/L : ℝ) : ℂ)).re ≤ B)
    (hnone : ∀ ρ, f ρ = 0 → ¬ InNearOneBox L ρ) :
    |(logDeriv f ((1+h : ℝ) : ℂ)).re| ≤ 676*B := by
  simpa only [nearOneZeroPole_sum_of_no_zero hf h0 hnone, sub_zero] using
    logDeriv_re_nearOne_error_le hf h0 hg hfe hstrip hL hh hh4 hbase

theorem logDeriv_re_error_le_of_unique_near_zero {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) (hg : HasSubquadraticGrowth f)
    (hfe : ∀ z, f (1-z) = f z) (hstrip : ∀ ρ, f ρ = 0 → ρ.re ≤ 1)
    {L h B : ℝ} (hL : 0 < L) (hh : 0 < h) (hh4 : h ≤ 4/L)
    (hbase : (logDeriv f ((1+1/L : ℝ) : ℂ)).re ≤ B)
    {ρ : ℂ} (hbox : InNearOneBox L ρ) (hm : zeroMultiplicity f ρ = 1)
    (hreal : ρ.im = 0) (hunique : ∀ τ, f τ = 0 → InNearOneBox L τ → τ = ρ) :
    |(logDeriv f ((1+h : ℝ) : ℂ)).re - 1/(1+h-ρ.re)| ≤ 676*B := by
  simpa only [nearOneZeroPole_sum_of_unique hf h0 hbox hm hreal hunique] using
    logDeriv_re_nearOne_error_le hf h0 hg hfe hstrip hL hh hh4 hbase

end OAI.PrimeDegreePackets.AnalyticGrowth
