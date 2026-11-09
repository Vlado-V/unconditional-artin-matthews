module

public import ArtinMatthews.SpectralABLCoshCancellation
public import ArtinMatthews.SpectralABLWindowAnalytic


set_option backward.privateInPublic true
@[expose] public section

/-! The literal ABL windows divided by the source cosh weight, with
removable values supplied by the proved Gamma cancellation factor. -/

noncomputable section
open Set
open scoped BigOperators

namespace ArtinMatthews

def spectralABLRegularBase (T Δ : ℝ) (z : ℂ) : ℂ :=
  (Complex.exp (-(((z-(T : ℂ))/(Δ : ℂ))^2)) +
    Complex.exp (-(((z+(T : ℂ))/(Δ : ℂ))^2)))/(T : ℂ)^2

def spectralABLExceptionalBase (a : ℝ) (A : ℕ) (z : ℂ) : ℂ :=
  (2*Complex.cos (2*z*(Real.log a : ℂ)))^2/(z^2+(2*(A : ℂ))^2)^(2*A)*
    ∏ k ∈ Finset.range A,(z^2+(((2*(k+1)+1 : ℕ) : ℂ)/2)^2)

def spectralABLRegularCorrected (T Δ : ℝ) (z : ℂ) : ℂ :=
  spectralABLRegularBase T Δ z*spectralABLCoshCancellation z

def spectralABLExceptionalCorrected (a : ℝ) (A : ℕ) (z : ℂ) : ℂ :=
  spectralABLExceptionalBase a A z*spectralABLCoshCancellation z

theorem spectralABLRegularWindow_factor (T Δ : ℝ) (z : ℂ) :
    spectralABLRegularWindow T Δ z = (z^2+1/4)*spectralABLRegularBase T Δ z := by
  unfold spectralABLRegularWindow spectralABLRegularBase
  ring

theorem spectralABLExceptionalWindow_factor (a : ℝ) (A : ℕ) (z : ℂ) :
    spectralABLExceptionalWindow a A z = (z^2+1/4)*spectralABLExceptionalBase a A z := by
  unfold spectralABLExceptionalWindow spectralABLExceptionalBase
  rw [Finset.prod_range_succ']
  norm_num
  ring

theorem spectralABLRegularCorrected_even (T Δ : ℝ) (z : ℂ) :
    spectralABLRegularCorrected T Δ (-z) = spectralABLRegularCorrected T Δ z := by
  unfold spectralABLRegularCorrected spectralABLRegularBase
  rw [spectralABLCoshCancellation_even,
    show (-z-(T : ℂ))/(Δ : ℂ) = -((z+(T : ℂ))/(Δ : ℂ)) by ring,
    show (-z+(T : ℂ))/(Δ : ℂ) = -((z-(T : ℂ))/(Δ : ℂ)) by ring]
  simp only [neg_sq]
  rw [add_comm (Complex.exp _) (Complex.exp _)]

theorem spectralABLExceptionalCorrected_even (a : ℝ) (A : ℕ) (z : ℂ) :
    spectralABLExceptionalCorrected a A (-z) = spectralABLExceptionalCorrected a A z := by
  unfold spectralABLExceptionalCorrected spectralABLExceptionalBase
  rw [spectralABLCoshCancellation_even,
    show 2*(-z)*(Real.log a : ℂ) = -(2*z*(Real.log a : ℂ)) by ring,Complex.cos_neg]
  simp only [neg_sq]

theorem spectralABLRegularCorrected_differentiableAt (T Δ : ℝ) (z : ℂ)
    (hz : |z.im| < 3/2) : DifferentiableAt ℂ (spectralABLRegularCorrected T Δ) z := by
  have hb : DifferentiableAt ℂ (spectralABLRegularBase T Δ) z := by
    unfold spectralABLRegularBase
    fun_prop
  exact hb.mul (spectralABLCoshCancellation_differentiableAt z hz)

theorem spectralABLExceptionalCorrected_differentiableAt (a : ℝ) {A : ℕ} (hA : 1 ≤ A) (z : ℂ)
    (hz : |z.im| < 3/2) : DifferentiableAt ℂ (spectralABLExceptionalCorrected a A) z := by
  have hA' : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hd := spectralABLExceptionalWindow_den_ne_zero A z (by linarith)
  apply DifferentiableAt.mul
  · unfold spectralABLExceptionalBase
    apply DifferentiableAt.mul
    · apply DifferentiableAt.div
      · fun_prop
      · fun_prop
      · exact pow_ne_zero _ hd
    · fun_prop
  · exact spectralABLCoshCancellation_differentiableAt z hz

theorem spectralABLRegularCorrected_mul_cosh (T Δ : ℝ) (z : ℂ) (hz : |z.im| < 1/2) :
    spectralABLRegularCorrected T Δ z*Complex.cosh ((Real.pi : ℂ)*z) = spectralABLRegularWindow T Δ z := by
  unfold spectralABLRegularCorrected
  rw [mul_assoc,spectralABLCoshCancellation_mul_cosh z hz,spectralABLRegularWindow_factor]
  ring

theorem spectralABLExceptionalCorrected_mul_cosh (a : ℝ) (A : ℕ) (z : ℂ) (hz : |z.im| < 1/2) :
    spectralABLExceptionalCorrected a A z*Complex.cosh ((Real.pi : ℂ)*z) = spectralABLExceptionalWindow a A z := by
  unfold spectralABLExceptionalCorrected
  rw [mul_assoc,spectralABLCoshCancellation_mul_cosh z hz,spectralABLExceptionalWindow_factor]
  ring

theorem spectralABLRegularCorrected_real (T Δ t : ℝ) :
    spectralABLRegularCorrected T Δ (t : ℂ) =
      spectralABLRegularWindow T Δ (t : ℂ)/(Real.cosh (Real.pi*t) : ℂ) := by
  have hc : (Real.cosh (Real.pi*t) : ℂ) ≠ 0 := by exact_mod_cast (Real.cosh_pos _).ne'
  apply (eq_div_iff hc).mpr
  simpa only [← Complex.ofReal_mul,← Complex.ofReal_cosh] using
    spectralABLRegularCorrected_mul_cosh T Δ (t : ℂ) (by norm_num)

theorem spectralABLExceptionalCorrected_real (a : ℝ) (A : ℕ) (t : ℝ) :
    spectralABLExceptionalCorrected a A (t : ℂ) =
      spectralABLExceptionalWindow a A (t : ℂ)/(Real.cosh (Real.pi*t) : ℂ) := by
  have hc : (Real.cosh (Real.pi*t) : ℂ) ≠ 0 := by exact_mod_cast (Real.cosh_pos _).ne'
  apply (eq_div_iff hc).mpr
  simpa only [← Complex.ofReal_mul,← Complex.ofReal_cosh] using
    spectralABLExceptionalCorrected_mul_cosh a A (t : ℂ) (by norm_num)

end ArtinMatthews
