module

public import ArtinMatthews.SpectralJForwardHolomorphic
public import ArtinMatthews.SpectralJForwardWeylNormalization
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp


set_option backward.privateInPublic true
@[expose] public section

/-! The literal forward transform and its hyperbolic spectral weight are
smooth on the real axis. Only the real-axis nonvanishing of cosh is used. -/
noncomputable section
open Set Complex
open scoped ContDiff

namespace ArtinMatthews

theorem spectralJForwardTransform_real_contDiff (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) :
    ContDiff ℝ ∞ (fun t : ℝ => spectralJForwardTransform f (t : ℂ)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  have ha : AnalyticAt ℂ (spectralJForwardTransform f) (t : ℂ) :=
    spectralJForwardTransform_analyticOnNhd f hf hc hp _ (by simp)
  have h : ContDiffAt ℂ ∞ (spectralJForwardTransform f) (t : ℂ) := ha.contDiffAt
  exact (h.restrict_scalars ℝ).comp t Complex.ofRealCLM.contDiff.contDiffAt

theorem spectralJForwardSpectralWeight_real_contDiff (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) :
    ContDiff ℝ ∞ (fun t : ℝ => spectralJForwardSpectralWeight f (t : ℂ)) := by
  have hDen : ContDiff ℝ ∞ (fun t : ℝ => Real.cosh (Real.pi*t)) :=
    Real.contDiff_cosh.comp (contDiff_const.mul contDiff_id)
  have hPref : ContDiff ℝ ∞ (fun t : ℝ => ((Real.pi/Real.cosh (Real.pi*t) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.div hDen (fun t => (Real.cosh_pos _).ne'))
  have he : (fun t : ℝ => spectralJForwardSpectralWeight f (t : ℂ)) =
      fun t : ℝ => ((Real.pi/Real.cosh (Real.pi*t) : ℝ) : ℂ)*spectralJForwardTransform f (t : ℂ) := by
    funext t
    rw [spectralJForwardSpectralWeight, ← Complex.ofReal_mul, ← Complex.ofReal_cosh, Complex.ofReal_div]
  rw [he]
  exact hPref.mul (spectralJForwardTransform_real_contDiff f hf hc hp)

end ArtinMatthews
