module

public import ArtinMatthews.SpectralGamma0EllipticNativeEquation
public import ArtinMatthews.SpectralGamma0CuspActual


set_option backward.privateInPublic true
@[expose] public section

/-! Actual basis vectors of the full all-height cuspidal mass kernel satisfy
the literal coordinate Laplace equation distributionally. Smoothness is not
assumed or asserted here; it is the remaining elliptic regularity step. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff InnerProductSpace

namespace ArtinMatthews

theorem gamma0FullCuspidalSpectralBasis_compact_weak_laplacian
    (N : ℕ) [NeZero N] (i : Gamma0AllHeightSpectralIndex N) (ψ : h2SmoothCompactSeeds) :
    inner ℂ (gamma0SmoothSeedMass N (h2SectionLaplacianSeed ψ))
      (gamma0FullCuspidalSpectralBasis N i).val =
      (gamma0AllHeightGradientSpectralValue N i : ℂ) *
        inner ℂ (gamma0SmoothSeedMass N ψ) (gamma0FullCuspidalSpectralBasis N i).val := by
  have he := gamma0Green_global_weak_laplacian N ψ (gamma0FullCuspidalSpectralBasis N i).val
  rw [gamma0FullCuspidalSpectralBasis_eigen,inner_smul_right,inner_add_left] at he
  have hc := congrArg (fun z : ℂ => i.1⁻¹*z) he
  simp only [← mul_assoc,inv_mul_cancel₀ (gamma0AllHeightSpectralValue_ne_zero N i),one_mul] at hc
  have hvalue : (gamma0AllHeightGradientSpectralValue N i : ℂ) = i.1⁻¹-1 := by
    simp only [gamma0AllHeightGradientSpectralValue,Complex.ofReal_sub,Complex.ofReal_inv,
      Complex.ofReal_one,gamma0AllHeightSpectralValue_real N i]
  rw [hvalue]
  linear_combination hc

theorem gamma0FullCuspidalSpectralBasis_twoCell_weak_laplacian
    (N : ℕ) [NeZero N] (i : Gamma0AllHeightSpectralIndex N)
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (ψ : h2SmoothCompactSeeds)
    (hs : tsupport ψ.val ⊆ hyperbolicCuspStrip (2*(N : ℝ)) Y) :
    (∫ z in hyperbolicCuspStrip (2*(N : ℝ)) Y,
      inner ℂ (h2SectionPositiveLaplacian ψ.val z)
        (gamma0CuspTwoCellMassRestriction N r Y hY (gamma0FullCuspidalSpectralBasis N i).val z)) =
      (gamma0AllHeightGradientSpectralValue N i : ℂ) *
        (∫ z in hyperbolicCuspStrip (2*(N : ℝ)) Y,
          inner ℂ (ψ.val z)
            (gamma0CuspTwoCellMassRestriction N r Y hY (gamma0FullCuspidalSpectralBasis N i).val z)) := by
  have hψ : Function.support (fun z => ψ.val z) ⊆ hyperbolicCuspStrip (2*(N : ℝ)) Y :=
    (subset_tsupport _).trans hs
  have hΔψ : Function.support (fun z => (h2SectionLaplacianSeed ψ).val z) ⊆
      hyperbolicCuspStrip (2*(N : ℝ)) Y :=
    (subset_tsupport _).trans ((h2SectionPositiveLaplacian_tsupport_subset ψ).trans hs)
  have he := gamma0FullCuspidalSpectralBasis_compact_weak_laplacian N i
    (modularTranslateSmoothSeed r ψ)
  rw [h2SectionLaplacianSeed_modular_pullback,
    gamma0Mass_inner_unfold_twoCell_integral N r Y hY (h2SectionLaplacianSeed ψ) hΔψ _,
    gamma0Mass_inner_unfold_twoCell_integral N r Y hY ψ hψ _] at he
  apply mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0)
  calc
    _ = (gamma0AllHeightGradientSpectralValue N i : ℂ) *
        (2*(∫ z in hyperbolicCuspStrip (2*(N : ℝ)) Y,
          inner ℂ (ψ.val z)
            (gamma0CuspTwoCellMassRestriction N r Y hY (gamma0FullCuspidalSpectralBasis N i).val z))) := he
    _ = _ := by ring

theorem gamma0FullCuspidalSpectralBasis_native_weak_laplacian
    (N : ℕ) [NeZero N] (i : Gamma0AllHeightSpectralIndex N)
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (χ : (Fin 2 → ℝ) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hs : tsupport χ ⊆ {x : Fin 2 → ℝ | x 0 ∈ Ioc 0 (2*(N : ℝ)) ∧ Y < x 1}) :
    (∫ z in hyperbolicCuspStrip (2*(N : ℝ)) Y,
      inner ℂ (z.im^2*spectralEllipticPositiveLaplacian χ
        (spectralEllipticCoordinates.symm (z.re,z.im)) : ℂ)
        (gamma0CuspTwoCellMassRestriction N r Y hY (gamma0FullCuspidalSpectralBasis N i).val z)) =
      (gamma0AllHeightGradientSpectralValue N i : ℂ) *
        (∫ z in hyperbolicCuspStrip (2*(N : ℝ)) Y,
          inner ℂ (χ (spectralEllipticCoordinates.symm (z.re,z.im)) : ℂ)
            (gamma0CuspTwoCellMassRestriction N r Y hY (gamma0FullCuspidalSpectralBasis N i).val z)) := by
  have hh : tsupport χ ⊆ {x : Fin 2 → ℝ | 0 < x 1} :=
    fun x hx => hY.trans (hs hx).2
  let ψ := spectralEllipticTestSeed χ hχ hcχ hh
  have hψ : tsupport ψ.val ⊆ hyperbolicCuspStrip (2*(N : ℝ)) Y := by
    intro z hz
    exact hs (spectralEllipticTestSeed_support χ hχ hcχ hh hz)
  simpa only [ψ,spectralEllipticTestSeed_apply,spectralEllipticTestSeed_laplacian] using
    gamma0FullCuspidalSpectralBasis_twoCell_weak_laplacian N i r Y hY ψ hψ

end ArtinMatthews
