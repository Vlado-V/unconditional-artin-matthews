module

public import ArtinMatthews.SpectralABLWindows
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import ArtinMatthews.SpectralABLExceptionalBound
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
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

namespace ArtinMatthews
open MeasureTheory Set
noncomputable section

private theorem shifted_gaussian_envelope (t m Δ : ℝ) (hΔ : 0 < Δ) :
    Real.exp (-(((t - m) / Δ) ^ 2)) ≤
      Real.exp (m ^ 2 / Δ ^ 2) * Real.exp (-(1 / (2 * Δ ^ 2)) * t ^ 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hs : -(t - m) ^ 2 ≤ m ^ 2 - t ^ 2 / 2 := by
    nlinarith [sq_nonneg (t - 2 * m)]
  convert div_le_div_of_nonneg_right hs (sq_nonneg Δ) using 1 <;>
    field_simp [hΔ.ne'] <;> ring

private theorem shifted_gaussian_first_cubic_integrable (m Δ : ℝ) (hΔ : 0 < Δ) :
    IntegrableOn (fun t : ℝ => t * (t ^ 2 + 1 / 4) *
      Real.exp (-(((t - m) / Δ) ^ 2))) (Ioi 0) := by
  let b : ℝ := 1 / (2 * Δ ^ 2)
  let C : ℝ := Real.exp (m ^ 2 / Δ ^ 2)
  have hb : 0 < b := by dsimp [b]; positivity
  have h1 : IntegrableOn (fun t : ℝ => t * Real.exp (-b * t ^ 2)) (Ioi 0) := by
    simpa using integrableOn_rpow_mul_exp_neg_mul_sq hb (s := 1) (by norm_num)
  have h3 : IntegrableOn (fun t : ℝ => t ^ 3 * Real.exp (-b * t ^ 2)) (Ioi 0) := by
    simpa only [Real.rpow_ofNat] using
      integrableOn_rpow_mul_exp_neg_mul_sq hb (s := 3) (by norm_num)
  have hmajor : IntegrableOn (fun t : ℝ => C * (t * (t ^ 2 + 1 / 4) *
      Real.exp (-b * t ^ 2))) (Ioi 0) := by
    have heq : (fun t : ℝ => C * (t * (t ^ 2 + 1 / 4) * Real.exp (-b * t ^ 2))) =
        (fun t : ℝ => C * (t ^ 3 * Real.exp (-b * t ^ 2) +
          (1 / 4) * (t * Real.exp (-b * t ^ 2)))) := by
      funext t
      ring
    rw [heq]
    exact (h3.add (h1.const_mul (1 / 4))).const_mul C
  apply hmajor.mono'
  · exact (by fun_prop : Measurable (fun t : ℝ => t * (t ^ 2 + 1 / 4) *
      Real.exp (-(((t - m) / Δ) ^ 2)))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := (show 0 < t from ht).le
    rw [Real.norm_of_nonneg (by positivity)]
    have henv := shifted_gaussian_envelope t m Δ hΔ
    change _ ≤ C * (t * (t ^ 2 + 1 / 4) * Real.exp (-b * t ^ 2))
    calc
      _ ≤ (t * (t ^ 2 + 1 / 4)) *
          (C * Real.exp (-b * t ^ 2)) :=
        mul_le_mul_of_nonneg_left henv (by positivity)
      _ = _ := by ring

theorem spectralABLRegularWindowReal_first_moment_integrable
    {T Δ : ℝ} (hT : 0 < T) (hΔ : 0 < Δ) :
    IntegrableOn (fun t : ℝ => t * spectralABLRegularWindowReal T Δ t) (Ioi 0) := by
  have hm := shifted_gaussian_first_cubic_integrable T Δ hΔ
  have hp := shifted_gaussian_first_cubic_integrable (-T) Δ hΔ
  have heq : (fun t : ℝ => t * spectralABLRegularWindowReal T Δ t) =
      (fun t : ℝ => (t * (t ^ 2 + 1 / 4) * Real.exp (-(((t - T) / Δ) ^ 2)) +
        t * (t ^ 2 + 1 / 4) * Real.exp (-(((t - -T) / Δ) ^ 2))) / T ^ 2) := by
    funext t
    unfold spectralABLRegularWindowReal
    simp only [sub_neg_eq_add]
    ring
  rw [heq]
  exact (hm.add hp).div_const (T ^ 2)

theorem spectralABLExceptionalWindowReal_first_moment_integrable
    (a : ℝ) {A : ℕ} (hA : 3 ≤ A) :
    IntegrableOn (fun t : ℝ => t * spectralABLExceptionalWindowReal a A t) (Ioi 0) := by
  let B : ℝ := spectralABLExceptionalBound A
  have hB : 0 ≤ B := by dsimp [B, spectralABLExceptionalBound]; positivity
  have hi : IntegrableOn (fun t : ℝ => B * (1 + t ^ 2)⁻¹) (Ioi 0) :=
    (integrable_inv_one_add_sq.const_mul B).integrableOn
  apply hi.mono'
  · exact (by unfold spectralABLExceptionalWindowReal; fun_prop :
      Measurable (fun t : ℝ => t * spectralABLExceptionalWindowReal a A t)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := ht.le
    rw [Real.norm_of_nonneg (mul_nonneg ht0 (spectralABLExceptionalWindowReal_nonneg a A t))]
    let u : ℝ := 1 + t ^ 2
    have hu : 0 < u := by dsimp [u]; positivity
    have hu1 : 1 ≤ u := by dsimp [u]; nlinarith [sq_nonneg t]
    have htu : t ≤ u := by dsimp [u]; nlinarith [sq_nonneg (t - 1)]
    have hpow : u ^ 2 ≤ u ^ (A - 1) := pow_le_pow_right₀ hu1 (by omega)
    have hdecay := spectralABLExceptionalWindowReal_decay a (show 1 ≤ A by omega) t
    change t * spectralABLExceptionalWindowReal a A t ≤ B * u⁻¹
    calc
      _ ≤ t * (B / u ^ (A - 1)) := mul_le_mul_of_nonneg_left hdecay ht0
      _ ≤ t * (B / u ^ 2) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left hB (pow_pos hu _) hpow) ht0
      _ = (B / u) * (t / u) := by field_simp <;> ring
      _ ≤ (B / u) * 1 := mul_le_mul_of_nonneg_left
        ((div_le_one hu).mpr htu) (div_nonneg hB hu.le)
      _ = B * u⁻¹ := by simp [div_eq_mul_inv]

end
end ArtinMatthews
