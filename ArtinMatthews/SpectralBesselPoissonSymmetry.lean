module

public import ArtinMatthews.SpectralBesselPoissonMoments
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


set_option backward.privateInPublic true
@[expose] public section

/-! Full-interval even and odd moments of the genuine Poisson weight. -/
noncomputable section
namespace ArtinMatthews

open MeasureTheory Set intervalIntegral Complex

@[simp] theorem spectralPoissonMoment_neg (ν : ℂ) (n : ℕ) (u : ℝ) :
    spectralPoissonMoment ν n (-u) = (-1 : ℂ) ^ n * spectralPoissonMoment ν n u := by
  unfold spectralPoissonMoment
  simp only [Complex.ofReal_neg]
  rw [neg_pow, neg_sq]
  ring

theorem spectralPoissonMoment_integrable_positive (ν : ℂ)
    (hν : -(1 / 2 : ℝ) < ν.re) (n : ℕ) :
    IntervalIntegrable (spectralPoissonMoment ν n) volume 0 1 := by
  have hw : IntervalIntegrable (fun u : ℝ => (1 - (u : ℂ) ^ 2) ^ (ν - 1 / 2)) volume 0 1 := by
    have h0 := (spectralPoisson_even_moment_beta ν hν 0).1
    change IntervalIntegrable (fun u : ℝ =>
      (u : ℂ) ^ 0 * (1 - (u : ℂ) ^ 2) ^ (ν - 1 / 2)) volume 0 1 at h0
    simpa only [pow_zero, one_mul] using h0
  have hh := hw.mul_continuousOn
    (show ContinuousOn (fun u : ℝ => (u : ℂ) ^ n) (uIcc 0 1) by fun_prop)
  convert hh using 1
  funext u
  dsimp only [spectralPoissonMoment]
  ring

theorem spectralPoissonMoment_integrable_negative (ν : ℂ)
    (hν : -(1 / 2 : ℝ) < ν.re) (n : ℕ) :
    IntervalIntegrable (spectralPoissonMoment ν n) volume (-1) 0 := by
  have hh := (IntervalIntegrable.iff_comp_neg).mp
    (spectralPoissonMoment_integrable_positive ν hν n)
  have hc := (hh.const_mul ((-1 : ℂ) ^ n)).symm
  simp only [neg_zero] at hc
  convert hc using 1
  funext u
  simp only [spectralPoissonMoment_neg]
  rw [← mul_assoc, ← mul_pow]
  norm_num

theorem spectralPoissonMoment_integrable (ν : ℂ)
    (hν : -(1 / 2 : ℝ) < ν.re) (n : ℕ) :
    IntervalIntegrable (spectralPoissonMoment ν n) volume (-1) 1 :=
  (spectralPoissonMoment_integrable_negative ν hν n).trans
    (spectralPoissonMoment_integrable_positive ν hν n)

/-- The negative interval contributes the exact parity sign. -/
theorem spectralPoissonMoment_integral_parity (ν : ℂ)
    (hν : -(1 / 2 : ℝ) < ν.re) (n : ℕ) :
    (∫ u : ℝ in (-1 : ℝ)..1, spectralPoissonMoment ν n u) =
      ((-1 : ℂ) ^ n + 1) * ∫ u : ℝ in (0 : ℝ)..1, spectralPoissonMoment ν n u := by
  have hneg : (∫ u : ℝ in (-1 : ℝ)..0, spectralPoissonMoment ν n u) =
      (-1 : ℂ) ^ n * ∫ u : ℝ in (0 : ℝ)..1, spectralPoissonMoment ν n u := by
    calc
      _ = ∫ u : ℝ in (0 : ℝ)..1, spectralPoissonMoment ν n (-u) := by
        simpa only [neg_zero] using
          (intervalIntegral.integral_comp_neg (f := spectralPoissonMoment ν n)
            (a := (0 : ℝ)) (b := 1)).symm
      _ = _ := by
        simp_rw [spectralPoissonMoment_neg]
        rw [intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (spectralPoissonMoment_integrable_negative ν hν n)
    (spectralPoissonMoment_integrable_positive ν hν n), hneg]
  ring

/-- Full even moment, with the exact Beta normalization. -/
theorem spectralPoisson_even_moment (ν : ℂ)
    (hν : -(1 / 2 : ℝ) < ν.re) (n : ℕ) :
    (∫ u : ℝ in (-1 : ℝ)..1, spectralPoissonMoment ν (2 * n) u) =
      Complex.betaIntegral ((n : ℂ) + 1 / 2) (ν + 1 / 2) := by
  rw [spectralPoissonMoment_integral_parity ν hν (2 * n),
    (spectralPoisson_even_moment_beta ν hν n).2]
  norm_num [pow_mul]
  field_simp

/-- Every odd moment vanishes by the actual reflection symmetry. -/
theorem spectralPoisson_odd_moment (ν : ℂ)
    (hν : -(1 / 2 : ℝ) < ν.re) (n : ℕ) :
    (∫ u : ℝ in (-1 : ℝ)..1, spectralPoissonMoment ν (2 * n + 1) u) = 0 := by
  rw [spectralPoissonMoment_integral_parity ν hν (2 * n + 1)]
  simp [pow_add, pow_mul]

end ArtinMatthews
