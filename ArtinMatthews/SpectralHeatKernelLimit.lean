module

public import ArtinMatthews.SpectralHeatArithmeticKernel
public import ArtinMatthews.SpectralHeatEnergyWeight
public import Mathlib.MeasureTheory.Integral.DominatedConvergence


set_option backward.privateInPublic true
@[expose] public section

/-! Fixed positive-argument Gaussian limits for the literal J/K
kernel. The required spectral L1 condition is retained explicitly. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace ArtinMatthews

def spectralABLBareKernel (H : ℂ → ℂ) (m n : ℤ) (X : ℝ) : ℂ :=
  ∫ t, spectralWeylIntegerSignMultiplier m n t X*H (t : ℂ) ∂spectralKLSpectralMeasure

theorem spectralABLBareKernel_integrable (H : ℂ → ℂ)
    (hH : Integrable (fun t : ℝ => H (t : ℂ)) spectralKLSpectralMeasure)
    (m n : ℤ) {X : ℝ} (hX : 0 < X) :
    Integrable (fun t : ℝ => spectralWeylIntegerSignMultiplier m n t X*H (t : ℂ))
      spectralKLSpectralMeasure := by
  obtain ⟨C,_,hb⟩ := spectralWeylIntegerSignMultiplier_bounded_positive m n hX
  apply hH.bdd_mul (spectralWeylIntegerSignMultiplier_measurable m n X).aestronglyMeasurable
  filter_upwards [spectralKLPositiveWeightMeasure_ae_pos spectralKLPlancherelWeight] with t ht
  exact hb t ht

theorem spectralABLHeatKernel_tendsto_bare (H : ℂ → ℂ)
    (hH : Integrable (fun t : ℝ => H (t : ℂ)) spectralKLSpectralMeasure)
    (m n : ℤ) {X : ℝ} (hX : 0 < X) :
    Tendsto (fun R : ℝ => spectralABLHeatKernel H R m n X) atTop
      (𝓝 (spectralABLBareKernel H m n X)) := by
  have hi := spectralABLBareKernel_integrable H hH m n hX
  unfold spectralABLHeatKernel spectralABLBareKernel
  apply tendsto_integral_filter_of_dominated_convergence
    (fun t : ℝ => ‖spectralWeylIntegerSignMultiplier m n t X*H (t : ℂ)‖)
  · exact Eventually.of_forall (fun R => hi.aestronglyMeasurable.mul
      (show AEStronglyMeasurable (fun t : ℝ => Complex.exp (-2*((t : ℂ)/(R : ℂ))^2))
        spectralKLSpectralMeasure from (show Measurable (fun t : ℝ => Complex.exp (-2*((t : ℂ)/(R : ℂ))^2)) from by fun_prop).aestronglyMeasurable))
  · exact Eventually.of_forall (fun R => Eventually.of_forall (fun t => by
      rw [norm_mul]
      apply mul_le_of_le_one_right (norm_nonneg _)
      rw [← spectralHeatEnergyWeight_principal]
      exact spectralHeatEnergyWeight_principal_norm_le R (1/4+t^2) (by nlinarith [sq_nonneg t])))
  · exact hi.norm
  · exact Eventually.of_forall (fun t => by
      have hg := spectralHeatEnergyWeight_tendsto (1/4+t^2)
      simp_rw [spectralHeatEnergyWeight_principal] at hg
      simpa only [mul_one] using tendsto_const_nhds.mul hg)

end ArtinMatthews
