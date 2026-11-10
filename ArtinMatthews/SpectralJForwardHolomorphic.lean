module

public import ArtinMatthews.SpectralBesselJCompactOrderIntegral
public import ArtinMatthews.SpectralBesselJOrderZeroDerivative
public import ArtinMatthews.SpectralJForwardTransform
public import ArtinMatthews.SpectralBesselJOrderJoint
public import ArtinMatthews.SpectralJDividedOrder
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


set_option backward.privateInPublic true
@[expose] public section

/-! Holomorphy of the actual divided J kernel and its compact dx/x transform.
The value at zero is the integral of the literal order derivative. -/
noncomputable section
open Set MeasureTheory Complex

namespace ArtinMatthews

theorem spectralJForwardKernel_zero_eq_poisson {x : ℝ} (hx : 0 < x) :
    spectralJForwardKernel 0 x = -(2/(Real.pi : ℂ))*spectralBesselJOrderDerivativeZero x := by
  rw [spectralJForwardKernel_zero, (spectral_besselJ_order_hasDerivAt_zero hx).deriv]

theorem spectralJForwardKernel_differentiableOn {x : ℝ} (hx : 0 < x) :
    DifferentiableOn ℂ (fun z => spectralJForwardKernel z x) {z : ℂ | |z.im| < 1} :=
  spectralJDividedOrder_differentiableOn (fun ν => Complex.besselJ ν (x : ℂ))
    (spectral_besselJ_order_differentiable hx)

theorem spectralJForwardTransform_eq_divided_order (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) (z : ℂ) :
    spectralJForwardTransform f z =
      if z = 0 then -(2/(Real.pi : ℂ))*deriv (spectralBesselJOrderTransform f) 0
      else (spectralBesselJOrderTransform f (-2*I*z)-spectralBesselJOrderTransform f (2*I*z))/
        (2*Complex.sin ((Real.pi : ℂ)*I*z)) := by
  by_cases hz : z = 0
  · subst z
    rw [ite_eq_left rfl, (spectralBesselJOrderTransform_hasDerivAt f hf hc hp 0).deriv,
      spectralJForwardTransform, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    change f x*spectralJForwardKernel 0 x/(x : ℂ) =
      -(2/(Real.pi : ℂ))*(f x*deriv (fun w => Complex.besselJ w (x : ℂ)) 0/(x : ℂ))
    rw [spectralJForwardKernel_zero]
    ring
  · let g₁ (x : ℝ) := f x*Complex.besselJ (-2*I*z) (x : ℂ)/(x : ℂ)
    let g₂ (x : ℝ) := f x*Complex.besselJ (2*I*z) (x : ℂ)/(x : ℂ)
    let c := 2*Complex.sin ((Real.pi : ℂ)*I*z)
    have h₁ : IntegrableOn g₁ (Ioi (0 : ℝ)) := spectralBesselJOrderTransform_integrable f hf hc hp _
    have h₂ : IntegrableOn g₂ (Ioi (0 : ℝ)) := spectralBesselJOrderTransform_integrable f hf hc hp _
    rw [ite_eq_right hz]
    change (∫ x in Ioi (0 : ℝ), f x*spectralJForwardKernel z x/(x : ℂ)) =
      ((∫ x in Ioi (0 : ℝ), g₁ x)-(∫ x in Ioi (0 : ℝ), g₂ x))/c
    rw [← integral_sub h₁ h₂]
    calc
      _ = ∫ x in Ioi (0 : ℝ), (g₁ x-g₂ x)*c⁻¹ := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        change f x*spectralJForwardKernel z x/(x : ℂ) = (g₁ x-g₂ x)*c⁻¹
        rw [spectralJForwardKernel_of_ne_zero hz]
        simp only [g₁,g₂,c,div_eq_mul_inv]
        ring
      _ = _ := by rw [integral_mul_const, div_eq_mul_inv]

theorem spectralJForwardTransform_differentiableOn (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) :
    DifferentiableOn ℂ (spectralJForwardTransform f) {z : ℂ | |z.im| < 1} :=
  (spectralJDividedOrder_differentiableOn (spectralBesselJOrderTransform f)
    (spectralBesselJOrderTransform_differentiable f hf hc hp)).congr
      (fun z _ => spectralJForwardTransform_eq_divided_order f hf hc hp z)

theorem spectralJForwardTransform_analyticOnNhd (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) :
    AnalyticOnNhd ℂ (spectralJForwardTransform f) {z : ℂ | |z.im| < 1} :=
  (spectralJForwardTransform_differentiableOn f hf hc hp).analyticOnNhd
    (isOpen_lt Complex.continuous_im.abs continuous_const)

end ArtinMatthews
