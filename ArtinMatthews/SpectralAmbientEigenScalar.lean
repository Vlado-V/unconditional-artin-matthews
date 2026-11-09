module

public import ArtinMatthews.SpectralAmbientEigenEquation
public import ArtinMatthews.SpectralGamma0EllipticScalarEquation


set_option backward.privateInPublic true
@[expose] public section

/-! The actual ambient eigen-equation in real scalar strip pairings. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff InnerProductSpace
namespace ArtinMatthews

theorem gamma0AmbientEigen_strip_scalar_weak_laplacian
    (N : ℕ) [NeZero N] (v : gamma0EnergySpace N) (eig : ℝ) (hl : 0 ≤ eig)
    (hG : gamma0Green N (gamma0EnergyInclusion N v) =
      (((eig + 1)⁻¹ : ℝ) : ℂ) • gamma0EnergyInclusion N v)
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (L : ℂ →L[ℝ] ℝ)
    (χ : (Fin 2 → ℝ) → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hs : tsupport χ ⊆ {x : Fin 2 → ℝ | x 0 ∈ Ioc 0 (2*(N:ℝ)) ∧ Y < x 1}) :
    (∫ p, (p.2^2*spectralEllipticPositiveLaplacian χ (spectralEllipticCoordinates.symm p))*
      L (gamma0CuspTwoCellCoordinateRestriction N r Y hY
        (gamma0EnergyInclusion N v) p)
        ∂cuspStripMeasure (2*(N:ℝ)) Y) =
      eig *
        ∫ p, χ (spectralEllipticCoordinates.symm p)*
          L (gamma0CuspTwoCellCoordinateRestriction N r Y hY
            (gamma0EnergyInclusion N v) p)
          ∂cuspStripMeasure (2*(N:ℝ)) Y := by
  let t : ℝ × ℝ → ℝ := fun p => χ (spectralEllipticCoordinates.symm p)
  let s : ℝ × ℝ → ℝ := fun p =>
    p.2^2*spectralEllipticPositiveLaplacian χ (spectralEllipticCoordinates.symm p)
  have ht : Continuous t := hχ.continuous.comp spectralEllipticCoordinates.symm.continuous
  have htc : HasCompactSupport t := hcχ.comp_homeomorph spectralEllipticCoordinates.symm.toHomeomorph
  have hsmooth : Continuous s :=
    (continuous_snd.pow 2).mul ((spectralEllipticPositiveLaplacian_smooth χ hχ).continuous.comp
      spectralEllipticCoordinates.symm.continuous)
  have hsc : HasCompactSupport s :=
    ((spectralEllipticPositiveLaplacian_compact χ hcχ).comp_homeomorph
      spectralEllipticCoordinates.symm.toHomeomorph).mul_left
  have he := gamma0AmbientEigen_native_weak_laplacian N v eig hl hG r Y hY χ hχ hcχ hs
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul] at he
  change (∫ z in hyperbolicCuspStrip (2*(N:ℝ)) Y, inner ℂ (s (z.re,z.im):ℂ)
      (gamma0CuspTwoCellMassRestriction N r Y hY (gamma0EnergyInclusion N v) z)) =
    (eig : ℂ) *
      ∫ z in hyperbolicCuspStrip (2*(N:ℝ)) Y, inner ℂ (t (z.re,z.im):ℂ)
        (gamma0CuspTwoCellMassRestriction N r Y hY (gamma0EnergyInclusion N v) z) at he
  simp only [gamma0CuspTwoCellMassRestriction_real_pairing] at he
  have hL := congrArg L he
  rw [← Complex.real_smul, L.map_smul,
    cuspStrip_real_projection_pairing _ hY hsmooth hsc L,
    cuspStrip_real_projection_pairing _ hY ht htc L] at hL
  exact hL

end ArtinMatthews
