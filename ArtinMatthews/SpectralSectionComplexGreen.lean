module

public import ArtinMatthews.SpectralSectionGradientRepresentation


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine complex Green identity for a compact smooth H² test section
against any actual smooth section, with the literal coordinate Laplacian. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff InnerProductSpace

namespace ArtinMatthews

theorem h2Section_compact_complex_green (ψ : h2SmoothCompactSeeds)
    (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun w : ℂ => F (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im}) :
    (∫ z : UpperHalfPlane, inner ℂ (h2SectionPositiveLaplacian ψ.val z) (F z)) =
      ∫ z : UpperHalfPlane, inner ℂ (h2SectionGradient ψ.val z) (h2SectionGradient F z) := by
  obtain ⟨Y,hY,φ,hφ,hc,_,hh,he⟩ := exists_smooth_plane_extension_of_compact_seed ψ
  let G := spectralSectionSmoothExtension Y F
  have hG : ContDiff ℝ ∞ G := spectralSectionSmoothExtension_contDiff hY F hF
  let D : ℝ × ℝ → ℂ := fun p => ∑ i : Fin 2,
    inner ℂ (fderiv ℝ φ p (spectralPlaneDirection i))
      (fderiv ℝ G p (spectralPlaneDirection i))
  have hDzero {p : ℝ × ℝ} (hp : ¬ Y < p.2) (i : Fin 2) :
      fderiv ℝ φ p (spectralPlaneDirection i) = 0 :=
    image_eq_zero_of_notMem_tsupport (f := fun q => fderiv ℝ φ q (spectralPlaneDirection i))
      (fun ht => hp (hh (tsupport_fderiv_apply_subset ℝ (spectralPlaneDirection i) ht)))
  have hLzero {p : ℝ × ℝ} (hp : ¬ Y < p.2) :
      spectralPlanePositiveHyperbolic φ p = 0 :=
    image_eq_zero_of_notMem_tsupport (fun ht => hp (hh
      (spectralPlanePositiveHyperbolic_tsupport_subset φ ht)))
  have hleft (z : UpperHalfPlane) : inner ℂ (h2SectionPositiveLaplacian ψ.val z) (F z) =
      inner ℂ (spectralPlanePositiveHyperbolic φ (z.re,z.im)) (G (z.re,z.im)) := by
    rw [h2SectionPositiveLaplacian_representation ψ.val φ he z]
    by_cases hz : Y < z.im
    · dsimp only [G]
      rw [spectralSectionSmoothExtension_at_upper hY F z hz.le]
    · rw [hLzero hz,inner_zero_left,inner_zero_left]
  have hright (z : UpperHalfPlane) :
      inner ℂ (h2SectionGradient ψ.val z) (h2SectionGradient F z) = z.im^2 • D (z.re,z.im) := by
    have hi (i : Fin 2) :
        inner ℂ (h2SectionGradient ψ.val z i) (h2SectionGradient F z i) =
          z.im^2 • inner ℂ (fderiv ℝ φ (z.re,z.im) (spectralPlaneDirection i))
            (fderiv ℝ G (z.re,z.im) (spectralPlaneDirection i)) := by
      rw [h2SectionGradient_representation ψ.val φ hφ he z i]
      by_cases hz : Y < z.im
      · rw [spectralSectionSmoothExtension_frame hY F hF z hz i]
        rw [inner_smul_left_eq_smul,inner_smul_right_eq_smul,smul_smul,pow_two]
      · rw [hDzero hz i,smul_zero,inner_zero_left,inner_zero_left,smul_zero]
    rw [PiLp.inner_apply]
    simp_rw [hi]
    exact Finset.smul_sum.symm
  have hpositive : tsupport φ ⊆ {p : ℝ × ℝ | 0 < p.2} :=
    fun p hp => hY.trans (hh hp)
  have hcancel : (∫ z : UpperHalfPlane, inner ℂ (h2SectionGradient ψ.val z)
      (h2SectionGradient F z)) = ∫ p, D p := by
    simp_rw [hright]
    apply upperHalfPlane_integral_height_sq
    intro p hp
    have hnot : ¬ Y < p.2 := fun hh => hp (hY.trans hh)
    simp only [D,hDzero hnot,inner_zero_left,Finset.sum_const_zero]
  calc
    _ = ∫ z : UpperHalfPlane, inner ℂ (spectralPlanePositiveHyperbolic φ (z.re,z.im))
        (G (z.re,z.im)) := integral_congr_ae (Filter.Eventually.of_forall hleft)
    _ = ∫ p, D p := h2_plane_complex_green φ G hφ hG hc hpositive
    _ = _ := hcancel.symm

end ArtinMatthews
