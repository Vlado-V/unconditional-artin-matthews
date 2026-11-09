module

public import ArtinMatthews.SpectralPlaneTestSeed
public import ArtinMatthews.SpectralSeparableLaplacian


set_option backward.privateInPublic true
@[expose] public section

/-! Literal compact smooth separable hyperbolic tests, with their support
and actual differential Laplacian discharged from the one-dimensional data. -/

noncomputable section
open Set
open scoped ContDiff

namespace ArtinMatthews

theorem spectralSeparablePlane_support (χ η : ℝ → ℂ) :
    tsupport (fun p : ℝ × ℝ => χ p.1 * η p.2) ⊆ tsupport χ ×ˢ tsupport η := by
  apply closure_minimal _ ((isClosed_tsupport χ).prod (isClosed_tsupport η))
  intro p hp
  exact ⟨subset_tsupport χ (mul_ne_zero_iff.mp hp).1,
    subset_tsupport η (mul_ne_zero_iff.mp hp).2⟩

theorem spectralSeparablePlane_compact (χ η : ℝ → ℂ)
    (hcχ : HasCompactSupport χ) (hcη : HasCompactSupport η) :
    HasCompactSupport (fun p : ℝ × ℝ => χ p.1 * η p.2) :=
  (hcχ.prod hcη).of_isClosed_subset (isClosed_tsupport _) (spectralSeparablePlane_support χ η)

def h2SeparableSmoothSeed (χ η : ℝ → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hη : ContDiff ℝ ∞ η)
    (hcχ : HasCompactSupport χ) (hcη : HasCompactSupport η)
    (hpos : tsupport η ⊆ Ioi (0 : ℝ)) : h2SmoothCompactSeeds :=
  h2SmoothSeedOfPlane (fun p : ℝ × ℝ => χ p.1 * η p.2)
    ((hχ.comp contDiff_fst).mul (hη.comp contDiff_snd))
    (spectralSeparablePlane_compact χ η hcχ hcη)
    (fun _ hp => hpos (spectralSeparablePlane_support χ η hp).2)

theorem h2SeparableSmoothSeed_apply (χ η : ℝ → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hη : ContDiff ℝ ∞ η)
    (hcχ : HasCompactSupport χ) (hcη : HasCompactSupport η)
    (hpos : tsupport η ⊆ Ioi (0 : ℝ)) (z : UpperHalfPlane) :
    (h2SeparableSmoothSeed χ η hχ hη hcχ hcη hpos).val z = χ z.re * η z.im := rfl

theorem h2SeparableSmoothSeed_support (χ η : ℝ → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hη : ContDiff ℝ ∞ η)
    (hcχ : HasCompactSupport χ) (hcη : HasCompactSupport η)
    (hpos : tsupport η ⊆ Ioi (0 : ℝ)) :
    tsupport (h2SeparableSmoothSeed χ η hχ hη hcχ hcη hpos).val ⊆
      (fun z : UpperHalfPlane => (z.re,z.im)) ⁻¹' (tsupport χ ×ˢ tsupport η) :=
  (h2SmoothSeedOfPlane_support _ _ _ _).trans (preimage_mono (spectralSeparablePlane_support χ η))

theorem h2SeparableSmoothSeed_laplacian (χ η : ℝ → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hη : ContDiff ℝ ∞ η)
    (hcχ : HasCompactSupport χ) (hcη : HasCompactSupport η)
    (hpos : tsupport η ⊆ Ioi (0 : ℝ)) (z : UpperHalfPlane) :
    h2SectionPositiveLaplacian (h2SeparableSmoothSeed χ η hχ hη hcχ hcη hpos).val z =
      -(z.im^2) • (deriv (deriv χ) z.re * η z.im + χ z.re * deriv (deriv η) z.im) :=
  h2SectionPositiveLaplacian_separable χ η hχ hη z

end ArtinMatthews
