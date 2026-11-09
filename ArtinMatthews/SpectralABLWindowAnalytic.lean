module

public import ArtinMatthews.SpectralABLWindows


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set
open scoped BigOperators
noncomputable section

theorem spectralABLExceptionalWindow_den_ne_zero (A : ℕ) (z : ℂ)
    (hz : |z.im| < 2 * (A : ℝ)) : z ^ 2 + (2 * (A : ℂ)) ^ 2 ≠ 0 := by
  intro hzero
  have hr := congrArg Complex.re hzero
  norm_num [pow_two, Complex.mul_re, Complex.mul_im] at hr
  have hp : 0 < (2 * (A : ℝ) - z.im) * (2 * (A : ℝ) + z.im) :=
    mul_pos (sub_pos.mpr (abs_lt.mp hz).2) (by linarith [(abs_lt.mp hz).1])
  nlinarith [sq_nonneg z.re]

theorem spectralABLExceptionalWindow_differentiableAt (a : ℝ) (A : ℕ) (z : ℂ)
    (hz : |z.im| < 2 * (A : ℝ)) :
    DifferentiableAt ℂ (spectralABLExceptionalWindow a A) z := by
  unfold spectralABLExceptionalWindow
  apply DifferentiableAt.mul
  · apply DifferentiableAt.div
    · fun_prop
    · fun_prop
    · exact pow_ne_zero _ (spectralABLExceptionalWindow_den_ne_zero A z hz)
  · fun_prop

theorem spectralABLExceptionalWindow_real_continuous (a : ℝ) {A : ℕ} (hA : 1 ≤ A) :
    Continuous (fun t : ℝ => spectralABLExceptionalWindow a A (t : ℂ)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have ht : |(t : ℂ).im| < 2 * (A : ℝ) := by
    have hA' : (1 : ℝ) ≤ A := by exact_mod_cast hA
    simp only [Complex.ofReal_im, abs_zero]
    linarith
  exact (spectralABLExceptionalWindow_differentiableAt a A (t : ℂ) ht).continuousAt.comp
    Complex.continuous_ofReal.continuousAt

theorem spectralABLRegularWindow_real_continuous (T Δ : ℝ) :
    Continuous (fun t : ℝ => spectralABLRegularWindow T Δ (t : ℂ)) :=
  (spectralABLRegularWindow_differentiable T Δ).continuous.comp Complex.continuous_ofReal

theorem spectralABLExceptionalPhase_eq_cpow {a : ℝ} (ha : 0 < a) (z : ℂ) :
    2 * Complex.cos (2 * z * (Real.log a : ℂ)) =
      (a : ℂ) ^ (2 * z * Complex.I) + (a : ℂ) ^ (-2 * z * Complex.I) := by
  have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  rw [Complex.two_cos, Complex.cpow_def_of_ne_zero ha0, Complex.cpow_def_of_ne_zero ha0,
    ← Complex.ofReal_log ha.le]
  congr 1 <;> congr 1 <;> ring

end
end ArtinMatthews
