module

public import ArtinMatthews.SpectralWeylCutoffCompact
public import ArtinMatthews.SpectralKLCompactInverse


set_option backward.privateInPublic true
@[expose] public section

/-! The completed KL analysis of every literal compact cutoff agrees
with its proved integral formula. The uncut input is an actual L2
function and no pointwise inverse representation is assumed. -/

noncomputable section
open Set MeasureTheory Filter
namespace ArtinMatthews

theorem spectralKLAnalysis_height_cutoff_ae {a : ℝ} (ha : 0 < a) (K : ℕ)
    (f : ℝ → ℂ) (hf : ContinuousOn f (Ioi (0 : ℝ)))
    (hL : MemLp f 2 spectralKLPhysicalMeasure) :
    spectralKLAnalysis (spectralWeylCutoffLp a K (hL.toLp f)) =ᵐ[spectralKLSpectralMeasure]
      spectralKLPhysicalAnalysisIntegral (spectralWeylProfileCutoff a K f) := by
  let g := spectralWeylProfileCutoff a K f
  have hc : Continuous g := spectralWeylProfileCutoff_continuous ha K f hf
  have hs : HasCompactSupport g := spectralWeylProfileCutoff_compact ha K f
  have hp : tsupport g ⊆ Ioi (0 : ℝ) := spectralWeylProfileCutoff_positive ha K f
  have hg := spectralKLPhysical_compact_memLp g hc hs hp
  have he : spectralWeylCutoffLp a K (hL.toLp f) = hg.toLp g := by
    apply Lp.ext
    filter_upwards [spectralWeylCutoffLp_ae a K (hL.toLp f),hL.coeFn_toLp,hg.coeFn_toLp]
      with x hx hf' hg'
    rw [hx,hg']
    change (spectralHeightAnnularPartial K (a*x) : ℂ)*(hL.toLp f) x =
      (spectralHeightAnnularPartial K (a*x) : ℂ)*f x
    rw [hf']
  rw [he]
  exact spectralKLAnalysis_compact_ae g hc hs hp

end ArtinMatthews
