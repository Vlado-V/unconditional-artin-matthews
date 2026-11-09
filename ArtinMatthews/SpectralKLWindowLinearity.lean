module

public import ArtinMatthews.SpectralKLInverseIEnvelope


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory
noncomputable section

theorem spectralKLWindowData_const_mul (c : ℂ) (h : ℂ → ℂ) (g : ℝ → ℂ) (t : ℝ) :
    spectralKLWindowData (fun z => c * h z) g t = c * spectralKLWindowData h g t := by
  unfold spectralKLWindowData
  ring

theorem spectralKLWindowSynthesis_const_mul (c : ℂ) (h : ℂ → ℂ) (g : ℝ → ℂ) (x : ℝ) :
    spectralKLWindowSynthesis (fun z => c * h z) g x = c * spectralKLWindowSynthesis h g x := by
  unfold spectralKLWindowSynthesis
  split_ifs with hx
  · unfold spectralKLWeightedSynthesis
    simp only [spectralKLWindowData_const_mul]
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    ring
  · simp only [mul_zero]

end
end ArtinMatthews
