module

public import ArtinMatthews.SpectralKLPowerAnalysis
public import ArtinMatthews.SpectralKLCoshFourier
public import Mathlib.MeasureTheory.Measure.OpenPos


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory Filter
noncomputable section

theorem spectralKLPhysicalAnalysisIntegral_even (f : ℝ → ℂ) (t : ℝ) :
    spectralKLPhysicalAnalysisIntegral f (-t) = spectralKLPhysicalAnalysisIntegral f t := by
  unfold spectralKLPhysicalAnalysisIntegral
  simp only [spectralKLRealKernel_even]

theorem spectralKLPower_analysis_eq (f F : ℝ → ℂ) (hf : Measurable f)
    (hfzero : ∀ x : ℝ, x ≤ 0 → f x = 0) (hLp : MemLp f 2 spectralKLPhysicalMeasure)
    (M B : ℝ) (hM : 0 ≤ M) (hB : 0 < B)
    (hpower : ∀ x : ℝ, 0 < x → ‖f x‖ ≤ M * x ^ B)
    (hF : Continuous F) (hEven : ∀ t : ℝ, F (-t) = F t)
    (hAnalysis : spectralKLAnalysis (hLp.toLp f) =ᵐ[spectralKLSpectralMeasure] F) :
    ∀ t : ℝ, spectralKLPhysicalAnalysisIntegral f t = F t := by
  have hmajor := spectralKLPower_majorant_integrable f hf hfzero M B hM hB hpower
  have hc := spectralKLAnalysis_continuous_of_majorant f hf hfzero hmajor
  have ha := (spectralKLAnalysis_majorant_ae f hf hfzero hmajor hLp).symm.trans hAnalysis
  have hw : AEMeasurable (fun t : ℝ => ENNReal.ofReal (spectralKLPlancherelWeight t))
      (volume.restrict (Ioi (0 : ℝ))) :=
    (ENNReal.measurable_ofReal.comp spectralKLPlancherelWeight_continuous.measurable).aemeasurable
  have hp : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      ENNReal.ofReal (spectralKLPlancherelWeight t) ≠ 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (ENNReal.ofReal_pos.mpr (spectralKLPlancherelWeight_pos ht)).ne'
  have hLeb : spectralKLPhysicalAnalysisIntegral f =ᵐ[volume.restrict (Ioi (0 : ℝ))] F :=
    (withDensity_ae_eq hw hp).mp ha
  have hpos : EqOn (spectralKLPhysicalAnalysisIntegral f) F (Ioi (0 : ℝ)) :=
    MeasureTheory.Measure.eqOn_open_of_ae_eq hLeb isOpen_Ioi hc.continuousOn hF.continuousOn
  have hnonneg : EqOn (spectralKLPhysicalAnalysisIntegral f) F (Ici (0 : ℝ)) := by
    simpa only [closure_Ioi] using hpos.closure hc hF
  intro t
  by_cases ht : 0 ≤ t
  · exact hnonneg ht
  · calc
      _ = spectralKLPhysicalAnalysisIntegral f (-t) := (spectralKLPhysicalAnalysisIntegral_even f t).symm
      _ = F (-t) := hnonneg (show (-t) ∈ Ici (0 : ℝ) by change 0 ≤ -t; linarith)
      _ = F t := hEven t

end
end ArtinMatthews
