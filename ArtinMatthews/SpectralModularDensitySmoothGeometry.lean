module

public import ArtinMatthews.SpectralGamma0Core
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff


set_option backward.privateInPublic true
@[expose] public section

/-! Real smooth coordinates for actual compact upper-half-plane seeds. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Manifold ContDiff CompactlySupported

namespace ArtinMatthews

instance h2_real_isManifold : IsManifold 𝓘(ℝ, ℂ) ∞ UpperHalfPlane :=
  UpperHalfPlane.isOpenEmbedding_coe.isManifold_singleton

theorem h2_real_contMDiffAt_ofComplex {z : ℂ} (hz : 0 < z.im) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ UpperHalfPlane.ofComplex z := by
  rw [contMDiffAt_iff]
  constructor
  · rw [ContinuousAt, nhds_induced, tendsto_comap_iff]
    refine Tendsto.congr' (UpperHalfPlane.eventuallyEq_coe_comp_ofComplex hz).symm ?_
    simpa [UpperHalfPlane.ofComplex_apply_of_im_pos hz] using! tendsto_id
  · simpa using! contDiffAt_id.congr_of_eventuallyEq
      (UpperHalfPlane.eventuallyEq_coe_comp_ofComplex hz)

theorem h2_real_contMDiff_coordinates {f : UpperHalfPlane → ℂ}
    (hf : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f) :
    ContDiffOn ℝ ∞ (fun z : ℂ => f (UpperHalfPlane.ofComplex z)) {z : ℂ | 0 < z.im} := by
  intro z hz
  exact ((hf (UpperHalfPlane.ofComplex z)).comp z (h2_real_contMDiffAt_ofComplex hz)).contDiffAt.contDiffWithinAt

def h2SmoothCompactSeedOfContMDiff (f : UpperHalfPlane → ℂ)
    (hf : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f) (hs : HasCompactSupport f) : h2SmoothCompactSeeds :=
  ⟨{ toFun := f, continuous_toFun := hf.continuous, hasCompactSupport' := hs },
    h2_real_contMDiff_coordinates hf⟩

@[simp] theorem h2SmoothCompactSeedOfContMDiff_apply (f : UpperHalfPlane → ℂ)
    (hf : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f) (hs : HasCompactSupport f) (z : UpperHalfPlane) :
    (h2SmoothCompactSeedOfContMDiff f hf hs).val z = f z := rfl

end ArtinMatthews
