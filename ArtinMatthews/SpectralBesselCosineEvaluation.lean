module

public import Mathlib.Analysis.SpecialFunctions.Bessel
public import ArtinMatthews.SpectralBesselPoisson
public import ArtinMatthews.SpectralBesselPoissonSymmetry
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

/-! The actual complex-order J function evaluates the even cosine integral.
This keeps the Gamma and factor-two normalization of Poisson's formula. -/

noncomputable section
open Set MeasureTheory intervalIntegral

namespace ArtinMatthews

theorem spectralPoissonCosine_integrable (ν x : ℂ) (hν : -(1/2 : ℝ) < ν.re) :
    IntervalIntegrable (fun u : ℝ => Complex.cos (x*u) * (1-(u : ℂ)^2)^(ν-1/2)) volume 0 1 := by
  have hw := spectralPoissonMoment_integrable_positive ν hν 0
  change IntervalIntegrable (fun u : ℝ => (u : ℂ)^0 * (1-(u : ℂ)^2)^(ν-1/2)) volume 0 1 at hw
  simp only [pow_zero,one_mul] at hw
  have h := hw.mul_continuousOn
    (show ContinuousOn (fun u : ℝ => Complex.cos (x*u)) (uIcc 0 1) by fun_prop)
  convert h using 1
  ext u
  ring

theorem spectralPoissonIntegral_eq_cosine (ν x : ℂ) (hν : -(1/2 : ℝ) < ν.re) :
    (∫ u : ℝ in (-1 : ℝ)..1,
      Complex.exp (Complex.I*x*u) * (1-(u : ℂ)^2)^(ν-1/2)) =
      2 * ∫ u : ℝ in (0 : ℝ)..1,
        Complex.cos (x*u) * (1-(u : ℂ)^2)^(ν-1/2) := by
  let w := fun u : ℝ => (1-(u : ℂ)^2)^(ν-1/2)
  have hw0 : IntervalIntegrable w volume 0 1 := by
    have h := spectralPoissonMoment_integrable_positive ν hν 0
    change IntervalIntegrable (fun u : ℝ => (u : ℂ)^0 * w u) volume 0 1 at h
    simpa only [pow_zero,one_mul] using h
  have hw1 : IntervalIntegrable w volume (-1) 0 := by
    have h := spectralPoissonMoment_integrable_negative ν hν 0
    change IntervalIntegrable (fun u : ℝ => (u : ℂ)^0 * w u) volume (-1) 0 at h
    simpa only [pow_zero,one_mul] using h
  have hpos : IntervalIntegrable (fun u : ℝ => Complex.exp (Complex.I*x*u)*w u) volume 0 1 := by
    convert hw0.mul_continuousOn (show ContinuousOn
      (fun u : ℝ => Complex.exp (Complex.I*x*u)) (uIcc 0 1) by fun_prop) using 1
    ext u
    ring
  have hneg : IntervalIntegrable (fun u : ℝ => Complex.exp (Complex.I*x*u)*w u) volume (-1) 0 := by
    convert hw1.mul_continuousOn (show ContinuousOn
      (fun u : ℝ => Complex.exp (Complex.I*x*u)) (uIcc (-1) 0) by fun_prop) using 1
    ext u
    ring
  have hminus : IntervalIntegrable (fun u : ℝ => Complex.exp (-(x*u)*Complex.I)*w u) volume 0 1 := by
    convert hw0.mul_continuousOn (show ContinuousOn
      (fun u : ℝ => Complex.exp (-(x*u)*Complex.I)) (uIcc 0 1) by fun_prop) using 1
    ext u
    ring
  have hreflect : (∫ u : ℝ in (-1 : ℝ)..0, Complex.exp (Complex.I*x*u)*w u) =
      ∫ u : ℝ in (0 : ℝ)..1, Complex.exp (-(x*u)*Complex.I)*w u := by
    calc
      _ = ∫ u : ℝ in (0 : ℝ)..1, Complex.exp (Complex.I*x*((-u : ℝ) : ℂ))*w (-u) := by
        simpa only [neg_zero] using (intervalIntegral.integral_comp_neg
          (f := fun u : ℝ => Complex.exp (Complex.I*x*u)*w u) (a := (0 : ℝ)) (b := 1)).symm
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro u _
        dsimp only
        have he : Complex.I*x*(-(u : ℂ)) = -(x*u)*Complex.I := by ring
        simp only [w,Complex.ofReal_neg,neg_sq,he]
  change (∫ u : ℝ in (-1 : ℝ)..1, Complex.exp (Complex.I*x*u)*w u) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals hneg hpos,hreflect,
    ← intervalIntegral.integral_add hminus hpos,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  have he : Complex.I*x*(u : ℂ) = (x*u)*Complex.I := by ring
  rw [he]
  have hcos := Complex.two_cos (x*u)
  change Complex.exp (-(x*u)*Complex.I)*w u + Complex.exp ((x*u)*Complex.I)*w u =
    2*(Complex.cos (x*u)*w u)
  rw [← mul_assoc 2, hcos]
  ring

theorem spectral_besselJ_cosine (ν x : ℂ) (hν : -(1/2 : ℝ) < ν.re) :
    Complex.besselJ ν x =
      (2*(x/2)^ν / ((Real.sqrt Real.pi : ℂ)*Complex.Gamma (ν+1/2))) *
        ∫ u : ℝ in (0 : ℝ)..1, Complex.cos (x*u)*(1-(u : ℂ)^2)^(ν-1/2) := by
  rw [spectral_besselJ_poisson ν x hν,spectralPoissonIntegral_eq_cosine ν x hν]
  ring

end ArtinMatthews
