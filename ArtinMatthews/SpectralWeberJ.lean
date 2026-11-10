module

public import ArtinMatthews.SpectralBesselI
public import Mathlib.Analysis.CStarAlgebra.Classes
public import ArtinMatthews.SpectralGaussianJEvaluation
public import ArtinMatthews.SpectralGaussianJSeries
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
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
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! Positive frequency dilation gives the actual Gaussian Weber J
formula on the full endpoint-integrability half-plane Re(nu)>-1/2. -/

noncomputable section
open Set MeasureTheory Filter

namespace ArtinMatthews

theorem spectralWeberJ_dilation_point (ν : ℂ) {p : ℝ} (hp : 0 < p) (x : ℝ) :
    Complex.exp (-((Real.sqrt p : ℂ)*(x : ℂ))^2)*
      Complex.besselJ (2*ν) (((1/Real.sqrt p : ℝ) : ℂ)*((Real.sqrt p : ℂ)*(x : ℂ))) =
    Complex.exp (-(p : ℂ)*(x : ℂ)^2)*Complex.besselJ (2*ν) (x : ℂ) := by
  have hq : (Real.sqrt p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hp).ne'
  have hsq : (Real.sqrt p : ℂ)^2 = (p : ℂ) := by exact_mod_cast Real.sq_sqrt hp.le
  rw [mul_pow,hsq,Complex.ofReal_div,Complex.ofReal_one]
  have harg : (1/(Real.sqrt p : ℂ))*((Real.sqrt p : ℂ)*(x : ℂ)) = (x : ℂ) := by
    field_simp
  rw [harg]
  simp only [neg_mul]

theorem spectralWeberJ_integrable (ν : ℂ) (hν : -(1/2 : ℝ) < ν.re)
    {p : ℝ} (hp : 0 < p) :
    IntegrableOn (fun x : ℝ => Complex.exp (-(p : ℂ)*(x : ℂ)^2)*Complex.besselJ (2*ν) (x : ℂ))
      (Ioi (0 : ℝ)) := by
  let F : ℝ → ℂ := fun x => Complex.exp (-(x : ℂ)^2)*
    Complex.besselJ (2*ν) (((1/Real.sqrt p : ℝ) : ℂ)*(x : ℂ))
  have hF : IntegrableOn F (Ioi (0 : ℝ)) :=
    spectralGaussianJ_integrable ν hν (one_div_pos.mpr (Real.sqrt_pos.mpr hp))
  have h := (integrableOn_Ioi_comp_mul_left_iff F 0 (Real.sqrt_pos.mpr hp)).mpr
    (by simpa only [mul_zero] using hF)
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x _
  simpa only [F,Complex.ofReal_mul] using spectralWeberJ_dilation_point ν hp x

theorem spectralBesselJ_gaussian_weber (ν : ℂ) (hν : -(1/2 : ℝ) < ν.re)
    {p : ℝ} (hp : 0 < p) :
    (∫ x in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(x : ℂ)^2)*Complex.besselJ (2*ν) (x : ℂ)) =
      ((Real.sqrt (Real.pi/p) : ℂ)/2)*Complex.exp (-((1/(8*p) : ℝ) : ℂ))*
        spectralBesselI ν (1/(8*p)) := by
  let q : ℝ := 1/Real.sqrt p
  let F : ℝ → ℂ := fun x => Complex.exp (-(x : ℂ)^2)*Complex.besselJ (2*ν) ((q : ℂ)*(x : ℂ))
  have hq : 0 < q := one_div_pos.mpr (Real.sqrt_pos.mpr hp)
  have hsq : (Real.sqrt p)^2 = p := Real.sq_sqrt hp.le
  have hroot : Real.sqrt p ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  have harg : q^2/8 = 1/(8*p) := by
    dsimp [q]
    field_simp
    nlinarith [hsq]
  have h := integral_comp_mul_left_Ioi F 0 (Real.sqrt_pos.mpr hp)
  have hl : (∫ x in Ioi (0 : ℝ), F (Real.sqrt p*x)) =
      ∫ x in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(x : ℂ)^2)*Complex.besselJ (2*ν) (x : ℂ) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    simpa only [F,q,Complex.ofReal_mul] using spectralWeberJ_dilation_point ν hp x
  rw [mul_zero,hl] at h
  rw [h,spectralGaussianJ_evaluation ν hν hq,harg,Complex.real_smul]
  have hr : (Real.sqrt (Real.pi/p) : ℂ) = (Real.sqrt Real.pi : ℂ)/(Real.sqrt p : ℂ) := by
    rw [Real.sqrt_div Real.pi_pos.le,Complex.ofReal_div]
  rw [hr,Complex.ofReal_inv]
  ring

end ArtinMatthews
