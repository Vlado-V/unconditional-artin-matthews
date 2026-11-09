module

public import ArtinMatthews.SpectralSectionPlaneSmoothExtension
public import ArtinMatthews.SpectralGamma0Core


set_option backward.privateInPublic true
@[expose] public section

/-! A compact smooth hyperbolic seed has a genuine compact smooth plane
extension whose support remains in the coordinate image of its actual
support.  Compactness supplies a strictly positive height threshold. -/

noncomputable section
open Set
open scoped ContDiff CompactlySupported

namespace ArtinMatthews

theorem h2_compact_seed_lower_height (ψ : h2SmoothCompactSeeds) :
    ∃ Y : ℝ, 0 < Y ∧ ∀ z ∈ tsupport ψ.val, 2 * Y ≤ z.im := by
  by_cases hn : (tsupport ψ.val).Nonempty
  · obtain ⟨z, _, hz⟩ := ψ.val.hasCompactSupport.exists_isMinOn hn
      UpperHalfPlane.continuous_im.continuousOn
    refine ⟨z.im / 2, by positivity, fun w hw => ?_⟩
    have hh : z.im ≤ w.im := hz hw
    linarith only [hh]
  · exact ⟨1, zero_lt_one, fun z hz => (hn ⟨z, hz⟩).elim⟩

/-- Global smooth extension with literal values on every hyperbolic point,
compact support, and support bounded away from the real boundary. -/
theorem exists_smooth_plane_extension_of_compact_seed (ψ : h2SmoothCompactSeeds) :
    ∃ (Y : ℝ), 0 < Y ∧ ∃ φ : ℝ × ℝ → ℂ,
      ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      tsupport φ ⊆ (fun z : UpperHalfPlane => (z.re, z.im)) '' tsupport ψ.val ∧
      tsupport φ ⊆ {p : ℝ × ℝ | Y < p.2} ∧
      ∀ z : UpperHalfPlane, φ (z.re, z.im) = ψ.val z := by
  obtain ⟨Y, hY, hheight⟩ := h2_compact_seed_lower_height ψ
  let φ := spectralSectionSmoothExtension Y ψ.val
  let K := (fun z : UpperHalfPlane => (z.re, z.im)) '' tsupport ψ.val
  have hK : IsCompact K := ψ.val.hasCompactSupport.image
    (UpperHalfPlane.continuous_re.prodMk UpperHalfPlane.continuous_im)
  have hs : Function.support φ ⊆ K := by
    intro p hp
    have hpheight : Y / 2 < p.2 := by
      by_contra h
      exact hp (spectralSectionSmoothExtension_zero hY ψ.val (not_lt.mp h))
    have hppos : 0 < p.2 := by linarith
    have him : 0 < (Complex.equivRealProdCLM.symm p).im := by
      simpa [Complex.equivRealProdCLM_symm_apply] using hppos
    let z := UpperHalfPlane.ofComplex (Complex.equivRealProdCLM.symm p)
    have hcoords : (z.re, z.im) = p := by
      dsimp only [z]
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos him]
      exact Complex.equivRealProdCLM.apply_symm_apply p
    have hψ : ψ.val z ≠ 0 := by
      intro hz
      apply hp
      change spectralSectionSmoothExtension Y ψ.val p = 0
      rw [← hcoords]
      simp only [spectralSectionSmoothExtension, spectralSectionPlane_at_upper, hz, mul_zero]
    exact ⟨z, subset_tsupport ψ.val hψ, hcoords⟩
  have hts : tsupport φ ⊆ K := closure_minimal hs hK.isClosed
  refine ⟨Y, hY, φ, spectralSectionSmoothExtension_contDiff hY ψ.val ψ.property,
    hK.of_isClosed_subset (isClosed_tsupport φ) hts, hts, ?_, ?_⟩
  · rintro p hp
    obtain ⟨z, hz, rfl⟩ := hts hp
    have hh := hheight z hz
    change Y < z.im
    linarith
  · intro z
    by_cases hz : ψ.val z = 0
    · simp only [φ, spectralSectionSmoothExtension, spectralSectionPlane_at_upper, hz, mul_zero]
    · have hh := hheight z (subset_tsupport ψ.val hz)
      exact spectralSectionSmoothExtension_at_upper hY ψ.val z (by linarith)

end ArtinMatthews
