module

public import ArtinMatthews.SpectralAmbientEllipticLocal
public import ArtinMatthews.SpectralGamma0EllipticStripPeriod


set_option backward.privateInPublic true
@[expose] public section

/-! Smooth periodic representatives of every actual ambient eigenvector. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff
namespace ArtinMatthews

theorem gamma0AmbientEigen_real_smooth_periodic_classical
    (N : ℕ) [NeZero N] (v : gamma0EnergySpace N) (eig : ℝ) (hl : 0 ≤ eig)
    (hG : gamma0Green N (gamma0EnergyInclusion N v) =
      (((eig + 1)⁻¹ : ℝ) : ℂ) • gamma0EnergyInclusion N v)
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (L : ℂ →L[ℝ] ℝ) :
    ∃ u : (Fin 2 → ℝ) → ℝ,
      ContDiffOn ℝ ∞ u (spectralEllipticOpenStrip (2*(N:ℝ)) Y) ∧
      (∀ᵐ y ∂volume, y ∈ spectralEllipticOpenStrip (2*(N:ℝ)) Y →
        u y = L (gamma0CuspTwoCellCoordinateRestriction N r Y hY
          (gamma0EnergyInclusion N v) (spectralEllipticCoordinates y))) ∧
      (∀ y ∈ spectralEllipticOpenStrip (N:ℝ) Y, u (y+Pi.single 0 (N:ℝ)) = u y) ∧
      ∀ y ∈ spectralEllipticOpenStrip (2*(N:ℝ)) Y,
        spectralEllipticPositiveLaplacian u y =
          eig / (y 1)^2 * u y := by
  obtain ⟨u,hu,huf,he⟩ := gamma0AmbientEigen_real_smooth_classical N v eig hl hG r Y hY L
  exact ⟨u,hu,huf,gamma0CuspTwoCell_real_representative_periodic N r Y hY
    (gamma0EnergyInclusion N v) L u hu.continuousOn huf,he⟩


end ArtinMatthews
