module

public import ArtinMatthews.SpectralGamma0EllipticNativeEquation
public import ArtinMatthews.SpectralGamma0EllipticTestRegularity
public import ArtinMatthews.SpectralGamma0EllipticStripPairing
public import ArtinMatthews.SpectralCuspSeparableCoordinates


set_option backward.privateInPublic true
@[expose] public section

/-! The actual Green equation projected onto an arbitrary real linear
component, in the literal weighted plane strip. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff InnerProductSpace
namespace ArtinMatthews

theorem gamma0CuspTwoCellMassRestriction_real_pairing (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (t : ℝ × ℝ → ℝ) (f : Gamma0RegionL2 N) :
    (∫ z in hyperbolicCuspStrip (2*(N:ℝ)) Y,
      inner ℂ (t (z.re,z.im) : ℂ) (gamma0CuspTwoCellMassRestriction N r Y hY f z)) =
      ∫ p, t p • gamma0CuspTwoCellCoordinateRestriction N r Y hY f p
        ∂cuspStripMeasure (2*(N:ℝ)) Y := by
  change (∫ z in hyperbolicCuspStrip (2*(N:ℝ)) Y,
      inner ℂ (t (z.re,z.im) : ℂ) (cuspHyperbolicPullback (2*(N:ℝ)) Y hY
        (gamma0CuspTwoCellCoordinateRestriction N r Y hY f) z)) = _
  rw [cuspHyperbolicPullback_pairing_coordinates (2*(N:ℝ)) Y hY (fun p => (t p : ℂ))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun p => by
    simp only [RCLike.inner_apply,Complex.conj_ofReal,Complex.real_smul,mul_comm]

theorem gamma0Green_strip_scalar_weak_laplacian (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (L : ℂ →L[ℝ] ℝ)
    (χ : (Fin 2 → ℝ) → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hs : tsupport χ ⊆ {x : Fin 2 → ℝ | x 0 ∈ Ioc 0 (2*(N:ℝ)) ∧ Y < x 1})
    (f : Gamma0RegionL2 N) :
    (∫ p, (p.2^2*spectralEllipticPositiveLaplacian χ (spectralEllipticCoordinates.symm p))*
      L (gamma0CuspTwoCellCoordinateRestriction N r Y hY (gamma0Green N f) p)
        ∂cuspStripMeasure (2*(N:ℝ)) Y) =
      ∫ p, χ (spectralEllipticCoordinates.symm p)*
        L (gamma0CuspTwoCellCoordinateRestriction N r Y hY (f-gamma0Green N f) p)
          ∂cuspStripMeasure (2*(N:ℝ)) Y := by
  let t : ℝ × ℝ → ℝ := fun p => χ (spectralEllipticCoordinates.symm p)
  let s : ℝ × ℝ → ℝ := fun p =>
    p.2^2*spectralEllipticPositiveLaplacian χ (spectralEllipticCoordinates.symm p)
  have ht : Continuous t := hχ.continuous.comp spectralEllipticCoordinates.symm.continuous
  have htc : HasCompactSupport t := hcχ.comp_homeomorph spectralEllipticCoordinates.symm.toHomeomorph
  have hsmooth : Continuous s := by
    exact (continuous_snd.pow 2).mul ((spectralEllipticPositiveLaplacian_smooth χ hχ).continuous.comp
      spectralEllipticCoordinates.symm.continuous)
  have hsc : HasCompactSupport s :=
    ((spectralEllipticPositiveLaplacian_compact χ hcχ).comp_homeomorph
      spectralEllipticCoordinates.symm.toHomeomorph).mul_left
  have he := gamma0Green_native_test_weak_laplacian N r Y hY χ hχ hcχ hs f
  simp only [← Complex.ofReal_pow,← Complex.ofReal_mul] at he
  change (∫ z in hyperbolicCuspStrip (2*(N:ℝ)) Y, inner ℂ (t (z.re,z.im):ℂ)
    (gamma0CuspTwoCellMassRestriction N r Y hY (gamma0Green N f) z)) +
    (∫ z in hyperbolicCuspStrip (2*(N:ℝ)) Y, inner ℂ (s (z.re,z.im):ℂ)
    (gamma0CuspTwoCellMassRestriction N r Y hY (gamma0Green N f) z)) =
    ∫ z in hyperbolicCuspStrip (2*(N:ℝ)) Y, inner ℂ (t (z.re,z.im):ℂ)
    (gamma0CuspTwoCellMassRestriction N r Y hY f z) at he
  simp only [gamma0CuspTwoCellMassRestriction_real_pairing] at he
  have hsub : (∫ p, t p • gamma0CuspTwoCellCoordinateRestriction N r Y hY
      (f-gamma0Green N f) p ∂cuspStripMeasure (2*(N:ℝ)) Y) =
      (∫ p, t p • gamma0CuspTwoCellCoordinateRestriction N r Y hY f p
        ∂cuspStripMeasure (2*(N:ℝ)) Y) -
      ∫ p, t p • gamma0CuspTwoCellCoordinateRestriction N r Y hY (gamma0Green N f) p
        ∂cuspStripMeasure (2*(N:ℝ)) Y := by
    rw [map_sub,← integral_sub
      (cuspStrip_compact_pairing_integrable _ hY ht htc _)
      (cuspStrip_compact_pairing_integrable _ hY ht htc _)]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub
      (gamma0CuspTwoCellCoordinateRestriction N r Y hY f)
      (gamma0CuspTwoCellCoordinateRestriction N r Y hY (gamma0Green N f))] with p hp
    rw [hp]
    exact smul_sub _ _ _
  have hh : (∫ p, s p • gamma0CuspTwoCellCoordinateRestriction N r Y hY
      (gamma0Green N f) p ∂cuspStripMeasure (2*(N:ℝ)) Y) =
      ∫ p, t p • gamma0CuspTwoCellCoordinateRestriction N r Y hY
        (f-gamma0Green N f) p ∂cuspStripMeasure (2*(N:ℝ)) Y := by
    rw [hsub]
    exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using he)
  have hhL := congrArg L hh
  simpa only [cuspStrip_real_projection_pairing _ hY hsmooth hsc L,
    cuspStrip_real_projection_pairing _ hY ht htc L,t,s] using hhL

end ArtinMatthews
