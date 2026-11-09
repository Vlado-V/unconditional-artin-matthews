module

public import ArtinMatthews.ShiftedVoronoiBesselLaplace
public import ArtinMatthews.SpectralBesselJAllX


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open MeasureTheory Set
noncomputable section

def spectralJGaussianKernel (x w : ℝ) : ℂ :=
  Complex.besselJ 0 (2 * (Real.sqrt ((x ^ 2 / 8) * w) : ℂ))

theorem spectral_besselJ_zero_bounded_nonneg :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 ≤ x → ‖Complex.besselJ 0 (x : ℂ)‖ ≤ C := by
  obtain ⟨B,hB,hbound⟩ := spectral_besselJ_vertical_allX 0 (by norm_num)
  refine ⟨max 1 B, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro x hx
  rcases eq_or_lt_of_le hx with hzero | hpos
  · rw [← hzero]
    simpa [Complex.besselJ_zero] using le_max_left (1 : ℝ) B
  · have h := hbound 0 x hpos
    norm_num at h
    exact h.trans (le_max_right _ _)

theorem spectralJGaussianKernel_continuous :
    Continuous (fun p : ℝ × ℝ => spectralJGaussianKernel p.1 p.2) := by
  have hJ : Continuous (Complex.besselJ (0 : ℂ)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    simpa only [Int.cast_zero] using (Complex.analyticAt_besselJ_int 0 z).continuousAt
  have hp : Continuous (fun p : ℝ × ℝ =>
      (2 : ℂ) * (Real.sqrt ((p.1 ^ 2 / 8) * p.2) : ℂ)) := by fun_prop
  exact hJ.comp hp

theorem spectralJGaussianKernel_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x w : ℝ, ‖spectralJGaussianKernel x w‖ ≤ C := by
  obtain ⟨C,hC,hbound⟩ := spectral_besselJ_zero_bounded_nonneg
  refine ⟨C,hC,?_⟩
  intro x w
  unfold spectralJGaussianKernel
  rw [show (2 : ℂ) * (Real.sqrt ((x ^ 2 / 8) * w) : ℂ) =
      ((2 * Real.sqrt ((x ^ 2 / 8) * w) : ℝ) : ℂ) by push_cast; rfl]
  exact hbound _ (by positivity)

theorem spectralJGaussianKernel_laplace (x Y : ℝ) (hY : 0 < Y) :
    (∫ w in Ioi (0 : ℝ), (Real.exp (-(Y * w)) : ℂ) * spectralJGaussianKernel x w) =
      ((1 / Y * Real.exp (-(x ^ 2 / 8) / Y) : ℝ) : ℂ) := by
  exact integral_exp_mul_besselJ_zero_sqrt Y (x ^ 2 / 8) hY (by positivity)

theorem spectralJGaussianKernel_argument (x w : ℝ) (hx : 0 ≤ x) (hw : 0 ≤ w) :
    2 * Real.sqrt ((x ^ 2 / 8) * w) = x * Real.sqrt (w / 2) := by
  have ha : 0 ≤ (x ^ 2 / 8) * w := by positivity
  have hb : 0 ≤ w / 2 := by positivity
  have hleft : 0 ≤ 2 * Real.sqrt ((x ^ 2 / 8) * w) := by positivity
  have hright : 0 ≤ x * Real.sqrt (w / 2) := by positivity
  apply (sq_eq_sq₀ hleft hright).mp
  rw [mul_pow, mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb]
  ring

end
end ArtinMatthews
