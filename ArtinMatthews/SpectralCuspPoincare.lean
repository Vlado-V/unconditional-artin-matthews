module

public import OAI.Analysis.Conductivity.Variational.IntervalMeanPoincare


set_option backward.privateInPublic true
@[expose] public section

/-!
The horizontal mean-zero inequality needed for compactness in an H² cusp.
The real interval theorem is reused verbatim from math-main.  This file extends
it to actual complex sections, with the derivative and mean taken on the
section itself.  No spectral estimate or eigenfunction expansion is assumed.
-/

noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace ArtinMatthews

/-- A complex horizontal section with zero constant term has its mass controlled
by its actual horizontal derivative.  Periodicity is unnecessary for this
inequality; the zero mean is the substantive cusp condition. -/
theorem cusp_section_poincare {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    {a b : ℝ} (hab : a < b) (hmean : (∫ x in a..b, f x) = 0) :
    (∫ x in a..b, ‖f x‖ ^ 2) ≤
      (b - a) ^ 2 * ∫ x in a..b, ‖deriv f x‖ ^ 2 := by
  have hre : ContDiff ℝ ∞ (fun x => (f x).re) := Complex.reCLM.contDiff.comp hf
  have him : ContDiff ℝ ∞ (fun x => (f x).im) := Complex.imCLM.contDiff.comp hf
  have hmr : (∫ x in a..b, (f x).re) = 0 := by
    change (∫ x in a..b, Complex.reCLM (f x)) = 0
    rw [Complex.reCLM.intervalIntegral_comp_comm (hf.continuous.intervalIntegrable a b),
      hmean]
    rfl
  have hmi : (∫ x in a..b, (f x).im) = 0 := by
    change (∫ x in a..b, Complex.imCLM (f x)) = 0
    rw [Complex.imCLM.intervalIntegral_comp_comm (hf.continuous.intervalIntegrable a b),
      hmean]
    rfl
  have hdr (x : ℝ) : deriv (fun x => (f x).re) x = (deriv f x).re :=
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt x
      ((hf.differentiable (by simp)) x).hasDerivAt).deriv
  have hdi (x : ℝ) : deriv (fun x => (f x).im) x = (deriv f x).im :=
    (Complex.imCLM.hasFDerivAt.comp_hasDerivAt x
      ((hf.differentiable (by simp)) x).hasDerivAt).deriv
  have hr := OAI.ScalarConductivity.smooth_interval_mean_poincare hre hab
  have hi := OAI.ScalarConductivity.smooth_interval_mean_poincare him hab
  simp only [hmr, hmi, zero_div, sub_zero, hdr, hdi] at hr hi
  have hs (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  simp_rw [hs]
  have hd := hf.continuous_deriv (by simp)
  rw [intervalIntegral.integral_add (f := fun x => (f x).re ^ 2)
    (g := fun x => (f x).im ^ 2)
    ((Complex.continuous_re.comp hf.continuous).pow 2 |>.intervalIntegrable a b)
    ((Complex.continuous_im.comp hf.continuous).pow 2 |>.intervalIntegrable a b),
    intervalIntegral.integral_add (f := fun x => (deriv f x).re ^ 2)
    (g := fun x => (deriv f x).im ^ 2)
    ((Complex.continuous_re.comp hd).pow 2 |>.intervalIntegrable a b)
    ((Complex.continuous_im.comp hd).pow 2 |>.intervalIntegrable a b), mul_add]
  exact add_le_add hr hi

end ArtinMatthews
