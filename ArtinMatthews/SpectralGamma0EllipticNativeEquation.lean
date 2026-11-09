module

public import ArtinMatthews.SpectralGamma0EllipticTests
public import ArtinMatthews.SpectralGamma0EllipticWeakLaplacian


set_option backward.privateInPublic true
@[expose] public section

/-! The literal native-coordinate distributional equation of the actual
Green vector, tested by every admissible compact smooth real test. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff InnerProductSpace

namespace ArtinMatthews

theorem gamma0Green_native_test_weak_laplacian (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (χ : (Fin 2 → ℝ) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hs : tsupport χ ⊆ {x : Fin 2 → ℝ | x 0 ∈ Ioc 0 (2*(N : ℝ)) ∧ Y < x 1})
    (f : Gamma0RegionL2 N) :
    (∫ z in hyperbolicCuspStrip (2*(N : ℝ)) Y,
      inner ℂ (χ (spectralEllipticCoordinates.symm (z.re,z.im)) : ℂ)
        (gamma0CuspTwoCellMassRestriction N r Y hY (gamma0Green N f) z)) +
    (∫ z in hyperbolicCuspStrip (2*(N : ℝ)) Y,
      inner ℂ (z.im^2*spectralEllipticPositiveLaplacian χ
        (spectralEllipticCoordinates.symm (z.re,z.im)) : ℂ)
        (gamma0CuspTwoCellMassRestriction N r Y hY (gamma0Green N f) z)) =
    ∫ z in hyperbolicCuspStrip (2*(N : ℝ)) Y,
      inner ℂ (χ (spectralEllipticCoordinates.symm (z.re,z.im)) : ℂ)
        (gamma0CuspTwoCellMassRestriction N r Y hY f z) := by
  have hh : tsupport χ ⊆ {x : Fin 2 → ℝ | 0 < x 1} :=
    fun x hx => hY.trans (hs hx).2
  let ψ := spectralEllipticTestSeed χ hχ hcχ hh
  have hψ : tsupport ψ.val ⊆ hyperbolicCuspStrip (2*(N : ℝ)) Y := by
    intro z hz
    exact hs (spectralEllipticTestSeed_support χ hχ hcχ hh hz)
  simpa only [ψ,spectralEllipticTestSeed_apply,spectralEllipticTestSeed_laplacian] using
    gamma0Green_twoCell_compact_weak_laplacian N r Y hY ψ hψ f

end ArtinMatthews
