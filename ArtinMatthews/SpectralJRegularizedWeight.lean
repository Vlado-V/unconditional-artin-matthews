module

public import ArtinMatthews.SpectralJRegularizer
public import ArtinMatthews.SpectralJForwardRealWeight
public import ArtinMatthews.SpectralABLEnergyWindows


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews

open Set Complex
open scoped ContDiff
noncomputable section

/-- The actual same-sign spectral weight with its first cosh poles removed.
The Gamma factor retains the value at those points. -/
def spectralJRegularizedWeight (f : ℝ → ℂ) (L : ℝ) (z : ℂ) : ℂ :=
  (Real.pi : ℂ) * spectralJForwardTransform f z * spectralABLCoshCancellation z *
    spectralJRegularizerPrimitive L (z ^ 2 + 1 / 4)

theorem spectralJRegularizedWeight_even (f : ℝ → ℂ) (L : ℝ) (z : ℂ) :
    spectralJRegularizedWeight f L (-z) = spectralJRegularizedWeight f L z := by
  simp only [spectralJRegularizedWeight, spectralJForwardTransform_even f z,
    spectralABLCoshCancellation_even, neg_sq]

theorem spectralJRegularizedWeight_differentiableAt (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) (L : ℝ)
    (z : ℂ) (hz : |z.im| < 1) :
    DifferentiableAt ℂ (spectralJRegularizedWeight f L) z := by
  have hb := (spectralJForwardTransform_analyticOnNhd f hf hc hp z hz).differentiableAt
  have hC := spectralABLCoshCancellation_differentiableAt z (by linarith)
  exact ((hb.const_mul (Real.pi : ℂ)).mul hC).mul
    ((spectralJRegularizerPrimitive_differentiable L).differentiableAt.comp z
      (by fun_prop))

theorem spectralJRegularizedWeight_analyticOnNhd (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) (L : ℝ) :
    AnalyticOnNhd ℂ (spectralJRegularizedWeight f L) {z : ℂ | |z.im| < 1} :=
  (show DifferentiableOn ℂ (spectralJRegularizedWeight f L) {z : ℂ | |z.im| < 1} from
    fun z hz => (spectralJRegularizedWeight_differentiableAt f hf hc hp L z hz).differentiableWithinAt
    ).analyticOnNhd (isOpen_lt Complex.continuous_im.abs continuous_const)

theorem spectralJRegularizedWeight_real_contDiff (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) (L : ℝ) :
    ContDiff ℝ ∞ (fun t : ℝ => spectralJRegularizedWeight f L (t : ℂ)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  have ha : AnalyticAt ℂ (spectralJRegularizedWeight f L) (t : ℂ) :=
    spectralJRegularizedWeight_analyticOnNhd f hf hc hp L _ (by simp)
  have h : ContDiffAt ℂ ∞ (spectralJRegularizedWeight f L) (t : ℂ) := ha.contDiffAt
  exact (h.restrict_scalars ℝ).comp t Complex.ofRealCLM.contDiff.contDiffAt

theorem spectralJRegularizedWeight_mul_cosh (f : ℝ → ℂ) (L : ℝ)
    (z : ℂ) (hz : |z.im| < 1 / 2) :
    spectralJRegularizedWeight f L z * Complex.cosh ((Real.pi : ℂ) * z) =
      (Real.pi : ℂ) * spectralJForwardTransform f z *
        (1 - Complex.exp (-(L : ℂ) * (z ^ 2 + 1 / 4))) := by
  calc
    _ = (Real.pi : ℂ) * spectralJForwardTransform f z *
        ((spectralABLCoshCancellation z * Complex.cosh ((Real.pi : ℂ) * z)) *
          spectralJRegularizerPrimitive L (z ^ 2 + 1 / 4)) := by
      unfold spectralJRegularizedWeight
      ring
    _ = _ := by
      rw [spectralABLCoshCancellation_mul_cosh z hz, spectralJRegularizerPrimitive_mul]

theorem spectralJRegularizedWeight_source_pos (f : ℝ → ℂ) (L l : ℝ) (hl : 0 < l) :
    spectralJRegularizedWeight f L (spectralSourceParameter l) =
      ((1 - Real.exp (-(L * l)) : ℝ) : ℂ) *
        spectralJForwardSpectralWeight f (spectralSourceParameter l) := by
  have hcosh := spectralSourceParameter_cosh_ne_zero l hl
  apply mul_right_cancel₀ hcosh
  rw [spectralJRegularizedWeight_mul_cosh f L _ (spectralSourceParameter_im_lt_half l hl)]
  have hS : spectralSourceParameter l ^ 2 + 1 / 4 = (l : ℂ) := by
    rw [spectralSourceParameter_sq]
    ring
  rw [hS, show -(L : ℂ) * (l : ℂ) = ((-(L * l) : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_exp]
  unfold spectralJForwardSpectralWeight
  field_simp [hcosh]
  push_cast
  ring

theorem spectralJRegularizedWeight_half_I (f : ℝ → ℂ) (L : ℝ) :
    spectralJRegularizedWeight f L (I / 2) =
      (L : ℂ) * spectralJForwardTransform f (I / 2) := by
  have hS : (I / 2) ^ 2 + 1 / 4 = (0 : ℂ) := by
    rw [div_pow, I_sq]
    norm_num
  rw [spectralJRegularizedWeight, spectralABLCoshCancellation_half_I,
    hS, spectralJRegularizerPrimitive_zero]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  <;> ring

end
end ArtinMatthews
