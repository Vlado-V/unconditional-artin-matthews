module

public import ArtinMatthews.SpectralKLCompactInverse


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory Filter
noncomputable section

theorem spectralKLBoundedMultiplier_memLp (f : Lp ℂ 2 spectralKLPhysicalMeasure)
    (h : ℝ → ℂ) (hm : AEStronglyMeasurable h spectralKLSpectralMeasure)
    (C : ℝ) (hb : ∀ t, ‖h t‖ ≤ C) :
    MemLp (fun t => h t * spectralKLAnalysis f t) 2 spectralKLSpectralMeasure := by
  apply (Lp.memLp (spectralKLAnalysis f)).of_le_mul (c := C)
    (hm.mul (Lp.aestronglyMeasurable _))
  exact Eventually.of_forall (fun t => by
    change ‖h t * spectralKLAnalysis f t‖ ≤ C * ‖spectralKLAnalysis f t‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hb t) (norm_nonneg _))

/-- The actual inverse unitary KL transform of bounded spectral multiplication. -/
def spectralKLBoundedMultiplierProfile (f : Lp ℂ 2 spectralKLPhysicalMeasure)
    (h : ℝ → ℂ) (hm : AEStronglyMeasurable h spectralKLSpectralMeasure)
    (C : ℝ) (hb : ∀ t, ‖h t‖ ≤ C) : Lp ℂ 2 spectralKLPhysicalMeasure :=
  spectralKLCompletedSynthesis
    ((spectralKLBoundedMultiplier_memLp f h hm C hb).toLp
      (fun t => h t * spectralKLAnalysis f t))

theorem spectralKLBoundedMultiplierProfile_analysis (f : Lp ℂ 2 spectralKLPhysicalMeasure)
    (h : ℝ → ℂ) (hm : AEStronglyMeasurable h spectralKLSpectralMeasure)
    (C : ℝ) (hb : ∀ t, ‖h t‖ ≤ C) :
    spectralKLAnalysis (spectralKLBoundedMultiplierProfile f h hm C hb) =
      (spectralKLBoundedMultiplier_memLp f h hm C hb).toLp
        (fun t => h t * spectralKLAnalysis f t) :=
  spectralKLAnalysis_synthesis _

theorem spectralKLBoundedMultiplierProfile_analysis_ae (f : Lp ℂ 2 spectralKLPhysicalMeasure)
    (h : ℝ → ℂ) (hm : AEStronglyMeasurable h spectralKLSpectralMeasure)
    (C : ℝ) (hb : ∀ t, ‖h t‖ ≤ C) :
    spectralKLAnalysis (spectralKLBoundedMultiplierProfile f h hm C hb) =ᵐ[spectralKLSpectralMeasure]
      (fun t => h t * spectralKLAnalysis f t) := by
  rw [spectralKLBoundedMultiplierProfile_analysis]
  exact MemLp.coeFn_toLp _

theorem spectralKLBoundedMultiplierProfile_compact_analysis
    (g : ℝ → ℂ) (hg : Continuous g) (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi (0 : ℝ))
    (h : ℝ → ℂ) (hm : AEStronglyMeasurable h spectralKLSpectralMeasure)
    (C : ℝ) (hb : ∀ t, ‖h t‖ ≤ C) :
    spectralKLAnalysis (spectralKLBoundedMultiplierProfile
      ((spectralKLPhysical_compact_memLp g hg hc hp).toLp g) h hm C hb) =ᵐ[spectralKLSpectralMeasure]
      (fun t => h t * ∫ x in Ioi (0 : ℝ),
        OAI.CubicEisenstein.schlafliBesselK ((t : ℂ) * Complex.I) x * g x / (x : ℂ)) := by
  filter_upwards [spectralKLBoundedMultiplierProfile_analysis_ae
    ((spectralKLPhysical_compact_memLp g hg hc hp).toLp g) h hm C hb,
    spectralKLAnalysis_compact_integral_ae g hg hc hp] with t hmul htransform
  rw [hmul, htransform]

end
end ArtinMatthews
