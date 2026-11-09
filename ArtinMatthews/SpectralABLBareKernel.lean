module

public import ArtinMatthews.SpectralABLBareIntegrability
public import ArtinMatthews.SpectralHeatKernelLimit


set_option backward.privateInPublic true
@[expose] public section

/-! Concrete removal of the Gaussian factor from each fixed positive
argument of the source J/K kernel. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace ArtinMatthews

theorem spectralABLRegularHeatKernel_tendsto (T Δ : ℝ) (hT : 0 < T) (hΔ : 0 < Δ)
    (m n : ℤ) {X : ℝ} (hX : 0 < X) :
    Tendsto (fun R : ℝ => spectralABLHeatKernel (spectralABLRegularCorrected T Δ) R m n X) atTop
      (𝓝 (spectralABLBareKernel (spectralABLRegularCorrected T Δ) m n X)) :=
  spectralABLHeatKernel_tendsto_bare _ (spectralABLRegularCorrected_integrable T Δ hT hΔ) m n hX

theorem spectralABLExceptionalHeatKernel_tendsto (a : ℝ) (A : ℕ) (hA : 3 ≤ A)
    (m n : ℤ) {X : ℝ} (hX : 0 < X) :
    Tendsto (fun R : ℝ => spectralABLHeatKernel (spectralABLExceptionalCorrected a A) R m n X) atTop
      (𝓝 (spectralABLBareKernel (spectralABLExceptionalCorrected a A) m n X)) :=
  spectralABLHeatKernel_tendsto_bare _ (spectralABLExceptionalCorrected_integrable a A hA) m n hX

end ArtinMatthews
