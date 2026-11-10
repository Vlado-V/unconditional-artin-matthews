module

public import ArtinMatthews.SpectralBesselHyperbolicEvaluation
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev


set_option backward.privateInPublic true
@[expose] public section

/-! An integrable local order-derivative majorant for the actual logarithmic
Schlaefli kernel. The two shifted orders control the two infinite tails. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace ArtinMatthews

theorem spectral_exp_order_derivative_bound (a b u : ℝ) (hab : |a-b| ≤ 1) :
    |u| *Real.exp (a*u) ≤ Real.exp ((b+2)*u)+Real.exp ((b-2)*u) := by
  have ha := (abs_le.mp hab).2
  have hb := (abs_le.mp hab).1
  by_cases hu : 0 ≤ u
  · have he : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
    have hm : a*u ≤ (b+1)*u := mul_le_mul_of_nonneg_right (by linarith) hu
    calc
      |u| *Real.exp (a*u) = u*Real.exp (a*u) := by rw [abs_of_nonneg hu]
      _ ≤ Real.exp u*Real.exp ((b+1)*u) :=
        mul_le_mul he (Real.exp_le_exp.mpr hm) (Real.exp_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp ((b+2)*u) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := le_add_of_nonneg_right (Real.exp_nonneg _)
  · have hun : u ≤ 0 := le_of_not_ge hu
    have he : -u ≤ Real.exp (-u) := by linarith [Real.add_one_le_exp (-u)]
    have hm : a*u ≤ (b-1)*u := mul_le_mul_of_nonpos_right (by linarith) hun
    calc
      |u| *Real.exp (a*u) = (-u)*Real.exp (a*u) := by rw [abs_of_nonpos hun]
      _ ≤ Real.exp (-u)*Real.exp ((b-1)*u) :=
        mul_le_mul he (Real.exp_le_exp.mpr hm) (Real.exp_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp ((b-2)*u) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := le_add_of_nonneg_left (Real.exp_nonneg _)

def spectralKOrderDerivativeKernel (ν : ℂ) (x u : ℝ) : ℂ :=
  (u : ℂ)*spectralKLogKernel ν x u

theorem spectralKOrderDerivativeKernel_bound (ν ν₀ : ℂ) (x u : ℝ)
    (hν : |ν.re-ν₀.re| ≤ 1) :
    ‖spectralKOrderDerivativeKernel ν x u‖ ≤
      ‖spectralKLogKernel (ν₀+2) x u‖+‖spectralKLogKernel (ν₀-2) x u‖ := by
  have h := mul_le_mul_of_nonneg_left
    (spectral_exp_order_derivative_bound ν.re ν₀.re u hν)
    (Real.exp_nonneg (-(x*Real.cosh u)))
  simp only [spectralKOrderDerivativeKernel,spectralKLogKernel,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,Complex.norm_exp,Complex.add_re,Complex.sub_re,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  change |u| * Real.exp (-(x*Real.cosh u)+ν.re*u) ≤
    Real.exp (-(x*Real.cosh u)+(ν₀.re+2)*u)+Real.exp (-(x*Real.cosh u)+(ν₀.re-2)*u)
  calc
    _ = Real.exp (-(x*Real.cosh u))*(|u| * Real.exp (ν.re*u)) := by
      rw [Real.exp_add]
      ring
    _ ≤ Real.exp (-(x*Real.cosh u))*(Real.exp ((ν₀.re+2)*u)+Real.exp ((ν₀.re-2)*u)) := h
    _ = _ := by rw [mul_add,← Real.exp_add,← Real.exp_add]

theorem spectralKOrderDerivativeKernel_majorant_integrable (ν : ℂ) {x : ℝ} (hx : 0 < x) :
    Integrable (fun u => ‖spectralKLogKernel (ν+2) x u‖+‖spectralKLogKernel (ν-2) x u‖) :=
  (spectralKLogKernel_integrable (ν+2) hx).norm.add
    (spectralKLogKernel_integrable (ν-2) hx).norm

end ArtinMatthews
