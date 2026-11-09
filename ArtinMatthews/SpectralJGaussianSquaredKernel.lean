module

public import ArtinMatthews.SpectralJFactorialDerivatives
public import ArtinMatthews.SpectralJGaussianKernel
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus


set_option backward.privateInPublic true
@[expose] public section

/-! The squared-coordinate kernel is the analytic extension of the literal
Gaussian kernel at (x=sqrt{s}). The flux equation also bounds its derivative
on the positive ray using only the uniform order-zero bound. -/

namespace ArtinMatthews
open Set MeasureTheory
noncomputable section

private def squareSeries (w : ℝ) (j : ℕ) (s : ℝ) : ℂ :=
  spectralJFactorialSeries j ((-(w / 8) * s : ℝ) : ℂ)

def spectralJGaussianSquaredKernel (w : ℝ) : ℝ → ℂ :=
  squareSeries w 0

theorem spectralJGaussianSquaredKernel_eq_gaussianKernel (w s : ℝ) (hw : 0 ≤ w) (hs : 0 ≤ s) :
    spectralJGaussianSquaredKernel w s = spectralJGaussianKernel (Real.sqrt s) w := by
  unfold spectralJGaussianSquaredKernel squareSeries spectralJGaussianKernel
  rw [Real.sq_sqrt hs,
    show -(w / 8) * s = -((s / 8) * w) by ring, Complex.ofReal_neg]
  exact spectralJFactorialSeries_zero_eq_besselJ _ (by positivity)

private theorem squareSeries_hasDerivAt (w : ℝ) (j : ℕ) (s : ℝ) :
    HasDerivAt (squareSeries w j) (((-(w / 8) : ℝ) : ℂ) * squareSeries w (j + 1) s) s := by
  let a := fun q : ℝ => -(w / 8) * q
  have ha : HasDerivAt a (-(w / 8)) s := by
    simpa only [a, mul_one] using (hasDerivAt_id' s).const_mul (-(w / 8))
  have hu := (spectralJFactorialSeries_hasDerivAt j (a s : ℂ)).comp_ofReal
  change HasDerivAt (fun q : ℝ => spectralJFactorialSeries j (a q : ℂ))
    (((-(w / 8) : ℝ) : ℂ) * spectralJFactorialSeries (j + 1) (a s : ℂ)) s
  simpa only [Function.comp_def, Complex.real_smul] using hu.scomp s ha

theorem spectralJGaussianSquaredKernel_differentiable (w : ℝ) :
    Differentiable ℝ (spectralJGaussianSquaredKernel w) :=
  fun s => (squareSeries_hasDerivAt w 0 s).differentiableAt

theorem spectralJGaussianSquaredKernel_deriv_continuous (w : ℝ) :
    Continuous (deriv (spectralJGaussianSquaredKernel w)) := by
  have he : deriv (spectralJGaussianSquaredKernel w) =
      fun s => (((-(w / 8) : ℝ) : ℂ) * squareSeries w 1 s) := by
    funext s
    exact (squareSeries_hasDerivAt w 0 s).deriv
  rw [he]
  have hU : Continuous (squareSeries w 1) :=
    continuous_iff_continuousAt.mpr fun s => (squareSeries_hasDerivAt w 1 s).continuousAt
  exact continuous_const.mul hU

theorem spectralJGaussianSquaredKernel_flux_hasDerivAt (w s : ℝ) :
    HasDerivAt (fun q : ℝ => (q : ℂ) * deriv (spectralJGaussianSquaredKernel w) q)
      (((-(w / 8) : ℝ) : ℂ) * spectralJGaussianSquaredKernel w s) s := by
  let c : ℂ := ((-(w / 8) : ℝ) : ℂ)
  have he : (fun q : ℝ => (q : ℂ) * deriv (spectralJGaussianSquaredKernel w) q) =
      fun q : ℝ => ((q : ℂ) * c) * squareSeries w 1 q := by
    funext q
    change (q : ℂ) * deriv (squareSeries w 0) q = _
    rw [(squareSeries_hasDerivAt w 0 q).deriv]
    exact (mul_assoc _ _ _).symm
  have hc : HasDerivAt (fun q : ℝ => (q : ℂ) * c) c s := by
    simpa only [Complex.ofReal_one, one_mul] using ((hasDerivAt_id' s).ofReal_comp).mul_const c
  rw [he]
  have h := hc.mul (squareSeries_hasDerivAt w 1 s)
  convert h using 1
  change c * squareSeries w 0 s =
    c * squareSeries w 1 s + (s : ℂ) * c * (c * squareSeries w 2 s)
  have hz : ((-(w / 8) * s : ℝ) : ℂ) = (s : ℂ) * c := by
    dsimp only [c]
    rw [Complex.ofReal_mul, mul_comm]
  have hrec : squareSeries w 1 s + (s : ℂ) * c * squareSeries w 2 s =
      squareSeries w 0 s := by
    unfold squareSeries
    rw [← hz]
    exact spectralJFactorialSeries_ode _
  rw [← hrec]
  ring

theorem spectralJGaussianSquaredKernel_bounds :
    ∃ C : ℝ, 0 < C ∧
      (∀ w s : ℝ, 0 ≤ w → 0 ≤ s → ‖spectralJGaussianSquaredKernel w s‖ ≤ C) ∧
      (∀ w s : ℝ, 0 ≤ w → 0 < s →
        ‖deriv (spectralJGaussianSquaredKernel w) s‖ ≤ (w / 8) * C) := by
  obtain ⟨C, hC, hbound⟩ := spectralJGaussianKernel_bound
  have hQ (w s : ℝ) (hw : 0 ≤ w) (hs : 0 ≤ s) :
      ‖spectralJGaussianSquaredKernel w s‖ ≤ C := by
    rw [spectralJGaussianSquaredKernel_eq_gaussianKernel w s hw hs]
    exact hbound _ _
  refine ⟨C, hC, hQ, ?_⟩
  intro w s hw hs
  let Q := spectralJGaussianSquaredKernel w
  let c : ℂ := ((-(w / 8) : ℝ) : ℂ)
  have hQcont : Continuous Q := (spectralJGaussianSquaredKernel_differentiable w).continuous
  have hcQ : Continuous (fun q => c * Q q) := continuous_const.mul hQcont
  have hFTC : (∫ q in (0 : ℝ)..s, c * Q q) = (s : ℂ) * deriv Q s - (0 : ℂ) * deriv Q 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun q _ => spectralJGaussianSquaredKernel_flux_hasDerivAt w q)
      (hcQ.intervalIntegrable 0 s)
  rw [intervalIntegral.integral_const_mul, zero_mul, sub_zero] at hFTC
  have hmass : ‖∫ q in (0 : ℝ)..s, Q q‖ ≤ C * s := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (f := Q)
      (a := (0 : ℝ)) (b := s) (C := C) (fun q hq => by
        rw [Set.uIoc_of_le hs.le] at hq
        exact hQ w q hw hq.1.le)
    simpa only [sub_zero, abs_of_pos hs] using h
  have hcn : ‖c‖ = w / 8 := by
    dsimp only [c]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity)]
  apply le_of_mul_le_mul_left (a := s) _ hs
  calc
    s * ‖deriv Q s‖ = ‖(s : ℂ) * deriv Q s‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    _ = ‖c * ∫ q in (0 : ℝ)..s, Q q‖ := congrArg norm hFTC.symm
    _ ≤ (w / 8) * (C * s) := by
      rw [norm_mul, hcn]
      exact mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = s * ((w / 8) * C) := by ring

end
end ArtinMatthews
