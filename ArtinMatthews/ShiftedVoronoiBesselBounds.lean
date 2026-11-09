module

public import ArtinMatthews.ShiftedVoronoiBessel


set_option backward.privateInPublic true
@[expose] public section

/-!
# An exponential majorant for the actual order-zero Bessel kernel

The intentionally coarse bound suffices to justify Laplace/Fubini arguments
for compactly supported source tests. It follows directly from the convergent
factorial series, without an assumed integral representation of `J₀`.
-/

noncomputable section
open Complex

namespace ArtinMatthews

theorem norm_besselJ_zero_sqrt_le_exp (t : ℝ) (ht : 0 ≤ t) :
    ‖Complex.besselJ 0 (2 * (Real.sqrt t : ℂ))‖ ≤ Real.exp t := by
  apply (hasSum_besselJ_zero_sqrt t ht).norm_le_of_bounded
    (by simpa only [← Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp t)
  intro n
  simp only [norm_div, norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ht, norm_natCast]
  have hf : (1 : ℝ) ≤ n.factorial := by
    exact_mod_cast (show 1 ≤ n.factorial from Nat.factorial_pos n)
  apply div_le_div_of_nonneg_left (pow_nonneg ht n) (by positivity)
  nlinarith

@[fun_prop]
theorem continuous_besselJ_zero : Continuous (Complex.besselJ 0) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  simpa only [Int.cast_zero] using (Complex.analyticAt_besselJ_int 0 z).continuousAt

@[fun_prop]
theorem continuous_besselJ_zero_sqrt_mul :
    Continuous (fun p : ℝ × ℝ ↦
      Complex.besselJ 0 (2 * (Real.sqrt (p.1 * p.2) : ℂ))) := by
  fun_prop

end ArtinMatthews
