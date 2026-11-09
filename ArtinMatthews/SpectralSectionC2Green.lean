module

public import ArtinMatthews.SpectralPlaneC2Green
public import ArtinMatthews.SpectralEisensteinRemainderPDE


set_option backward.privateInPublic true
@[expose] public section

/-! The literal compact-test Laplacian transfer for any C² hyperbolic
section. The test cutoff supplies compactness; no smooth source is assumed. -/
noncomputable section
open Set Filter Topology MeasureTheory
open scoped ContDiff InnerProductSpace
namespace ArtinMatthews

theorem spectralCompactInner_integrable (f g : ℝ×ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g) (hs : HasCompactSupport f) :
    Integrable (fun p => inner ℂ (f p) (g p)) := by
  apply (hf.inner hg).integrable_of_hasCompactSupport
  apply hs.mono'
  intro p hp
  by_contra hn
  exact hp (by
    change inner ℂ (f p) (g p)=0
    rw [image_eq_zero_of_notMem_tsupport hn,inner_zero_left])

theorem spectralPlaneSecond_continuous_C2 (F : ℝ×ℝ → ℂ) (hF : ContDiff ℝ 2 F) (i : Fin 2) :
    Continuous (spectralPlaneSecond F i) := by
  have hD : ContDiff ℝ 1 (fun p => fderiv ℝ F p (spectralPlaneDirection i)) :=
    (hF.fderiv_right (by norm_num : (1:ℕ∞ω)+1≤2)).clm_apply contDiff_const
  exact (hD.continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem spectralPlanePositiveSecond_transfer_C2 (φ F : ℝ×ℝ → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hF : ContDiff ℝ 2 F) (hs : HasCompactSupport φ) :
    (∫ p, inner ℂ (spectralPlanePositiveSecond φ p) (F p))=
      ∫ p, inner ℂ (φ p) (spectralPlanePositiveSecond F p) := by
  have hL (i : Fin 2) : Integrable (fun p => inner ℂ (spectralPlaneSecond φ i p) (F p)) :=
    spectralCompactInner_integrable _ _ (spectralPlaneSecond_contDiff φ hφ i).continuous
      hF.continuous (spectralPlaneSecond_compact φ hs i)
  have hR (i : Fin 2) : Integrable (fun p => inner ℂ (φ p) (spectralPlaneSecond F i p)) :=
    spectralCompactInner_integrable _ _ hφ.continuous (spectralPlaneSecond_continuous_C2 F hF i) hs
  simp only [spectralPlanePositiveSecond,inner_neg_left,inner_neg_right,sum_inner,inner_sum]
  rw [integral_neg,integral_neg,integral_finsetSum _ (fun i _ => hL i),
    integral_finsetSum _ (fun i _ => hR i)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact spectralPlaneSecond_transfer_C2 φ F hφ hF hs i

theorem h2Plane_laplacian_transfer_C2 (φ F : ℝ×ℝ → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hF : ContDiff ℝ 2 F) (hs : HasCompactSupport φ)
    (hpositive : tsupport φ ⊆ {p : ℝ×ℝ | 0 < p.2}) :
    (∫ z : UpperHalfPlane, inner ℂ (spectralPlanePositiveHyperbolic φ (z.re,z.im)) (F (z.re,z.im)))=
      ∫ z : UpperHalfPlane, inner ℂ (φ (z.re,z.im)) (spectralPlanePositiveHyperbolic F (z.re,z.im)) := by
  have hφ0 {p : ℝ×ℝ} (hp : ¬ 0 < p.2) : φ p=0 :=
    image_eq_zero_of_notMem_tsupport (fun ht => hp (hpositive ht))
  have hΔ0 {p : ℝ×ℝ} (hp : ¬ 0 < p.2) : spectralPlanePositiveSecond φ p=0 := by
    have hD (i : Fin 2) : spectralPlaneSecond φ i p=0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro ht
      exact hp (hpositive (tsupport_fderiv_apply_subset ℝ (spectralPlaneDirection i)
        (tsupport_fderiv_apply_subset ℝ (spectralPlaneDirection i) ht)))
    simp only [spectralPlanePositiveSecond,hD,Finset.sum_const_zero,neg_zero]
  have hleft := upperHalfPlane_integral_height_sq
    (fun p => inner ℂ (spectralPlanePositiveSecond φ p) (F p))
    (fun p hp => by rw [hΔ0 hp,inner_zero_left])
  have hright := upperHalfPlane_integral_height_sq
    (fun p => inner ℂ (φ p) (spectralPlanePositiveSecond F p))
    (fun p hp => by rw [hφ0 hp,inner_zero_left])
  simp_rw [spectralPlanePositiveHyperbolic,inner_smul_left_eq_smul,inner_smul_right_eq_smul]
  rw [hleft,hright]
  exact spectralPlanePositiveSecond_transfer_C2 φ F hφ hF hs

theorem spectralSectionSmoothExtension_C2 {Y : ℝ} (hY : 0 < Y) (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ 2 (fun z : ℂ => F (UpperHalfPlane.ofComplex z)) {z | 0 < z.im}) :
    ContDiff ℝ 2 (spectralSectionSmoothExtension Y F) := by
  have hχ : ContDiff ℝ 2 (fun p : ℝ×ℝ => (spectralHeightTransition Y p.2:ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp
      (Real.smoothTransition.contDiff.comp (by fun_prop))
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : 0 < p.2
  · exact hχ.contDiffAt.mul ((spectralSectionPlane_C2 F hF).contDiffAt
      ((isOpen_lt continuous_const continuous_snd).mem_nhds hp))
  · have he : spectralSectionSmoothExtension Y F =ᶠ[𝓝 p] (fun _ => (0:ℂ)) := by
      filter_upwards [(isOpen_lt continuous_snd continuous_const).mem_nhds (show p.2 < Y/2 by linarith)] with q hq
      exact spectralSectionSmoothExtension_zero hY F hq.le
    exact contDiffAt_const.congr_of_eventuallyEq he

theorem h2Section_laplacian_transfer_C2 (ψ : h2SmoothCompactSeeds) (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ 2 (fun z : ℂ => F (UpperHalfPlane.ofComplex z)) {z | 0 < z.im}) :
    (∫ z : UpperHalfPlane, inner ℂ (h2SectionPositiveLaplacian ψ.val z) (F z))=
      ∫ z : UpperHalfPlane, inner ℂ (ψ.val z) (h2SectionPositiveLaplacian F z) := by
  obtain ⟨Y,hY,φ,hφ,hc,_,hh,he⟩ := exists_smooth_plane_extension_of_compact_seed ψ
  let G := spectralSectionSmoothExtension Y F
  have hG : ContDiff ℝ 2 G := spectralSectionSmoothExtension_C2 hY F hF
  have hφ0 (z : UpperHalfPlane) (hz : ¬ Y < z.im) : φ (z.re,z.im)=0 :=
    image_eq_zero_of_notMem_tsupport (fun ht => hz (hh ht))
  have hΔ0 (z : UpperHalfPlane) (hz : ¬ Y < z.im) : spectralPlanePositiveHyperbolic φ (z.re,z.im)=0 :=
    image_eq_zero_of_notMem_tsupport (fun ht => hz (hh (spectralPlanePositiveHyperbolic_tsupport_subset φ ht)))
  have hleft (z : UpperHalfPlane) : inner ℂ (h2SectionPositiveLaplacian ψ.val z) (F z)=
      inner ℂ (spectralPlanePositiveHyperbolic φ (z.re,z.im)) (G (z.re,z.im)) := by
    rw [h2SectionPositiveLaplacian_representation ψ.val φ he]
    by_cases hz : Y < z.im
    · dsimp only [G]
      rw [spectralSectionSmoothExtension_at_upper hY F z hz.le]
    · rw [hΔ0 z hz,inner_zero_left,inner_zero_left]
  have hright (z : UpperHalfPlane) : inner ℂ (ψ.val z) (h2SectionPositiveLaplacian F z)=
      inner ℂ (φ (z.re,z.im)) (spectralPlanePositiveHyperbolic G (z.re,z.im)) := by
    rw [← he]
    by_cases hz : Y < z.im
    · have hgerm : G =ᶠ[𝓝 (z.re,z.im)] spectralSectionPlane F := by
        filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hz] with p hp
        exact spectralSectionSmoothExtension_eq hY F hp.le
      rw [spectralPlanePositiveHyperbolic_congr_of_eventuallyEq _ _ hgerm]
      rfl
    · rw [hφ0 z hz,inner_zero_left,inner_zero_left]
  calc
    _=∫ z : UpperHalfPlane, inner ℂ (spectralPlanePositiveHyperbolic φ (z.re,z.im)) (G (z.re,z.im)) :=
      integral_congr_ae (Filter.Eventually.of_forall hleft)
    _=∫ z : UpperHalfPlane, inner ℂ (φ (z.re,z.im)) (spectralPlanePositiveHyperbolic G (z.re,z.im)) :=
      h2Plane_laplacian_transfer_C2 φ G hφ hG hc (fun p hp => hY.trans (hh hp))
    _=_ := integral_congr_ae (Filter.Eventually.of_forall (fun z => (hright z).symm))

end ArtinMatthews
