module

public import ArtinMatthews.SpectralSectionComplexGreen


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine differential Green identity on a modular chart, with all
boundary terms absent because the actual test support lies in its interior. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff InnerProductSpace MatrixGroups

namespace ArtinMatthews

theorem h2SectionPositiveLaplacian_zero_off_support (ψ : h2SmoothCompactSeeds)
    {z : UpperHalfPlane} (hz : z ∉ tsupport ψ.val) :
    h2SectionPositiveLaplacian ψ.val z = 0 := by
  obtain ⟨_,_,φ,_,_,hs,_,he⟩ := exists_smooth_plane_extension_of_compact_seed ψ
  rw [h2SectionPositiveLaplacian_representation ψ.val φ he z]
  apply image_eq_zero_of_notMem_tsupport
  intro ht
  obtain ⟨w,hw,heq⟩ := hs (spectralPlanePositiveHyperbolic_tsupport_subset φ ht)
  have hwz : w = z := UpperHalfPlane.ext (Complex.ext
    (congrArg Prod.fst heq) (congrArg Prod.snd heq))
  exact hz (hwz ▸ hw)

theorem h2SectionGradient_zero_off_support (F : UpperHalfPlane → ℂ)
    {z : UpperHalfPlane} (hz : z ∉ tsupport F) : h2SectionGradient F z = 0 := by
  apply norm_eq_zero.mp
  have h := h2SectionGradient_norm_sq F z
  rw [h2SectionEnergy_eq_zero_of_notMem_tsupport F hz] at h
  nlinarith [norm_nonneg (h2SectionGradient F z)]

theorem h2Section_modular_complex_green (ψ : h2SmoothCompactSeeds)
    (hψ : tsupport ψ.val ⊆ ModularGroup.fd) (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun w : ℂ => F (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im}) :
    (∫ z in ModularGroup.fd, inner ℂ (h2SectionPositiveLaplacian ψ.val z) (F z)) =
      ∫ z in ModularGroup.fd, inner ℂ (h2SectionGradient ψ.val z) (h2SectionGradient F z) := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz =>
    by rw [h2SectionPositiveLaplacian_zero_off_support ψ (fun ht => hz (hψ ht)),
      inner_zero_left])]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz =>
    by rw [h2SectionGradient_zero_off_support ψ.val (fun ht => hz (hψ ht)),
      inner_zero_left])]
  exact h2Section_compact_complex_green ψ F hF

end ArtinMatthews
