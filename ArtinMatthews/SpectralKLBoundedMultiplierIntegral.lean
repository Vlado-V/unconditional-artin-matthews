module

public import ArtinMatthews.SpectralKLWindowSynthesisL2


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory Filter
open scoped ContDiff
noncomputable section

theorem spectralKLBoundedMultiplierProfile_integral_ae (h : ℂ → ℂ) (g : ℝ → ℂ)
    (hh : ContDiff ℝ ∞ (fun t : ℝ => h (t : ℂ))) (C : ℝ)
    (hbound : ∀ t : ℝ, ‖h (t : ℂ)‖ ≤ C)
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi (0 : ℝ)) :
    spectralKLBoundedMultiplierProfile
      ((spectralKLPhysical_compact_memLp g hg.continuous hc hp).toLp g)
      (fun t : ℝ => h (t : ℂ)) hh.continuous.aestronglyMeasurable C hbound
        =ᵐ[spectralKLPhysicalMeasure] spectralKLWindowSynthesis h g := by
  let G : Lp ℂ 2 spectralKLPhysicalMeasure :=
    (spectralKLPhysical_compact_memLp g hg.continuous hc hp).toLp g
  let A := spectralKLBoundedMultiplier_memLp G (fun t : ℝ => h (t : ℂ))
    hh.continuous.aestronglyMeasurable C hbound
  let B := spectralKLWindowData_memLp h g hh.continuous C hbound hg.continuous hc hp
  have heq : A.toLp (fun t : ℝ => h (t : ℂ) * spectralKLAnalysis G t) =
      B.toLp (spectralKLWindowData h g) := by
    apply Lp.ext
    filter_upwards [A.coeFn_toLp, B.coeFn_toLp,
      spectralKLAnalysis_compact_ae g hg.continuous hc hp] with t htA htB htG
    rw [htA, htB]
    rw [htG, spectralKLWindowData, spectralKLCompactOrderTransform_imaginary g hp]
  change spectralKLCompletedSynthesis (A.toLp _) =ᵐ[spectralKLPhysicalMeasure] _
  rw [heq]
  exact spectralKLWindowSynthesis_inverse_ae h g hh C hbound hg hc hp

end
end ArtinMatthews
