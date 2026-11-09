module

public import ArtinMatthews.SpectralSectionModularGreen


set_option backward.privateInPublic true
@[expose] public section

/-! The actual differential Laplacian preserves genuine compact smooth
hyperbolic test sections. No independent regularity or support is assumed. -/

noncomputable section
open Set MeasureTheory
open scoped CompactlySupported ContDiff

namespace ArtinMatthews

theorem h2SectionPositiveLaplacian_continuous (ψ : h2SmoothCompactSeeds) :
    Continuous (h2SectionPositiveLaplacian ψ.val) := by
  obtain ⟨_,_,φ,hφ,_,_,_,he⟩ := exists_smooth_plane_extension_of_compact_seed ψ
  have heq : h2SectionPositiveLaplacian ψ.val =
      fun z : UpperHalfPlane => spectralPlanePositiveHyperbolic φ (z.re,z.im) :=
    funext (h2SectionPositiveLaplacian_representation ψ.val φ he)
  rw [heq]
  exact (spectralPlanePositiveHyperbolic_contDiff φ hφ).continuous.comp
    (UpperHalfPlane.continuous_re.prodMk UpperHalfPlane.continuous_im)

theorem h2SectionPositiveLaplacian_tsupport_subset (ψ : h2SmoothCompactSeeds) :
    tsupport (h2SectionPositiveLaplacian ψ.val) ⊆ tsupport ψ.val := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro z hz
  by_contra hn
  exact hz (h2SectionPositiveLaplacian_zero_off_support ψ hn)

theorem h2SectionPositiveLaplacian_smooth (ψ : h2SmoothCompactSeeds) :
    ContDiffOn ℝ ∞ (fun w : ℂ => h2SectionPositiveLaplacian ψ.val (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im} := by
  obtain ⟨_,_,φ,hφ,_,_,_,he⟩ := exists_smooth_plane_extension_of_compact_seed ψ
  have hh := (spectralPlanePositiveHyperbolic_contDiff φ hφ).comp Complex.equivRealProdCLM.contDiff
  apply hh.contDiffOn.congr
  intro w hw
  rw [h2SectionPositiveLaplacian_representation ψ.val φ he]
  simp only [UpperHalfPlane.ofComplex_apply_of_im_pos hw,UpperHalfPlane.mk_re,
    UpperHalfPlane.mk_im,Complex.equivRealProdCLM_apply,Function.comp_apply]

def h2SectionLaplacianSeed (ψ : h2SmoothCompactSeeds) : h2SmoothCompactSeeds :=
  ⟨{ toFun := h2SectionPositiveLaplacian ψ.val
     continuous_toFun := h2SectionPositiveLaplacian_continuous ψ
     hasCompactSupport' := ψ.val.hasCompactSupport.of_isClosed_subset
       (isClosed_tsupport _) (h2SectionPositiveLaplacian_tsupport_subset ψ) },
    h2SectionPositiveLaplacian_smooth ψ⟩

theorem h2SectionLaplacianSeed_apply (ψ : h2SmoothCompactSeeds) (z : UpperHalfPlane) :
    (h2SectionLaplacianSeed ψ).val z = h2SectionPositiveLaplacian ψ.val z := rfl

end ArtinMatthews
