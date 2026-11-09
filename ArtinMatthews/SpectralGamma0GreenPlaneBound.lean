module

public import ArtinMatthews.SpectralGamma0GreenCompactBound
public import ArtinMatthews.SpectralGamma0EllipticEigenPlane
public import ArtinMatthews.SpectralGamma0SpectralCutoff


set_option backward.privateInPublic true
@[expose] public section

/-! Point evaluation of actual smooth Green representatives on compact plane sets. -/
noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff
namespace ArtinMatthews

theorem gamma0Green_plane_compact_bound
    (N : ℕ) [NeZero N] (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKΩ : K ⊆ {p | 0 < p.1 ∧ p.1 < 2*(N:ℝ) ∧ Y < p.2}) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : Gamma0RegionL2 N) (F : ℝ × ℝ → ℂ),
      ContDiffOn ℝ ∞ F {p | 0 < p.1 ∧ p.1 < 2*(N:ℝ) ∧ Y < p.2} →
      (∀ᵐ p ∂volume, (0 < p.1 ∧ p.1 < 2*(N:ℝ) ∧ Y < p.2) →
        F p = gamma0CuspTwoCellCoordinateRestriction N r Y hY
          (gamma0Green N f) p) →
      ∀ p ∈ K, ‖F p‖ ≤ C*‖f‖ := by
  let K0 := spectralEllipticCoordinates.symm '' K
  have hK0 : IsCompact K0 := hK.image spectralEllipticCoordinates.symm.continuous
  have hK0Ω : K0 ⊆ spectralEllipticOpenStrip (2*(N:ℝ)) Y := by
    rintro x ⟨p,hp,rfl⟩
    exact hKΩ hp
  obtain ⟨C,hC,hb⟩ := gamma0Green_compact_complex_bound N r Y hY hK0 hK0Ω
  refine ⟨C,hC,?_⟩
  intro f F hF hFae p hp
  let G := fun x => F (spectralEllipticCoordinates x)
  have hG : ContDiffOn ℝ ∞ G (spectralEllipticOpenStrip (2*(N:ℝ)) Y) :=
    hF.comp spectralEllipticCoordinates.contDiff.contDiffOn (fun _ hx => hx)
  have hGa : ∀ᵐ x ∂volume, x ∈ spectralEllipticOpenStrip (2*(N:ℝ)) Y →
      G x = gamma0CuspTwoCellCoordinateRestriction N r Y hY
        (gamma0Green N f) (spectralEllipticCoordinates x) :=
    spectralEllipticCoordinates_measurePreserving.quasiMeasurePreserving.ae hFae
  have he := hb f G hG hGa (spectralEllipticCoordinates.symm p) ⟨p,hp,rfl⟩
  simpa only [G,ContinuousLinearEquiv.apply_symm_apply] using he

end ArtinMatthews
