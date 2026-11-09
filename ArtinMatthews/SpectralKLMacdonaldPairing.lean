module

public import ArtinMatthews.SpectralKLMacdonaldAnalysis


set_option backward.privateInPublic true
@[expose] public section

/-! Actual Hilbert-space pairing of the Gaussian-Weyl physical profile.
This uses the proved noncompact analysis calibration and the KL isometry. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein

namespace ArtinMatthews

theorem spectralKLMacdonaldPairing_integrable {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (F : Lp ℂ 2 spectralKLPhysicalMeasure) :
    Integrable (fun t : ℝ => star (2*schlafliBesselK ((t : ℂ)*Complex.I) x*
      schlafliBesselK ((t : ℂ)*Complex.I) y)*spectralKLAnalysis F t) spectralKLSpectralMeasure := by
  let P := (spectralKLMacdonaldProfile_memLp hx hy).toLp (spectralKLMacdonaldProfile x y)
  have hi := L2.integrable_inner (𝕜 := ℂ) (spectralKLAnalysis P) (spectralKLAnalysis F)
  apply hi.congr
  filter_upwards [spectralKLMacdonaldProfile_completed_analysis hx hy] with t ht
  rw [RCLike.inner_apply,ht]
  exact mul_comm _ _

theorem spectralKLMacdonaldPairing {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (F : Lp ℂ 2 spectralKLPhysicalMeasure) :
    inner ℂ ((spectralKLMacdonaldProfile_memLp hx hy).toLp (spectralKLMacdonaldProfile x y)) F =
      ∫ t : ℝ, star (2*schlafliBesselK ((t : ℂ)*Complex.I) x*
        schlafliBesselK ((t : ℂ)*Complex.I) y)*spectralKLAnalysis F t ∂spectralKLSpectralMeasure := by
  let P := (spectralKLMacdonaldProfile_memLp hx hy).toLp (spectralKLMacdonaldProfile x y)
  have h := spectralKLUnitary.inner_map_map (spectralKLAnalysis P) (spectralKLAnalysis F)
  have hpair : inner ℂ P F = inner ℂ (spectralKLAnalysis P) (spectralKLAnalysis F) := by
    simpa only [spectralKLUnitary_apply,spectralKLSynthesis_analysis] using h
  rw [hpair,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [spectralKLMacdonaldProfile_completed_analysis hx hy] with t ht
  rw [RCLike.inner_apply,ht]
  exact mul_comm _ _

end ArtinMatthews
