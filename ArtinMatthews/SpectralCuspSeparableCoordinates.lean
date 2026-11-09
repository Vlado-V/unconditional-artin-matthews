module

public import ArtinMatthews.SpectralCuspTwoCellHyperbolic


set_option backward.privateInPublic true
@[expose] public section

/-! Exact measurable-coordinate transport of completed compact-test pairings.
No pointwise continuity is imposed on the completed strip vector. -/
namespace ArtinMatthews
open MeasureTheory Set Filter
open scoped ENNReal MatrixGroups InnerProductSpace
noncomputable section

theorem cusp_coordinates_measurableEmbedding :
    MeasurableEmbedding (fun z : UpperHalfPlane => (z.re, z.im)) :=
  Complex.measurableEquivRealProd.measurableEmbedding.comp UpperHalfPlane.measurableEmbedding_coe

theorem cuspHyperbolicPullback_pairing_coordinates (w Y : ℝ) (hY : 0 < Y)
    (t : ℝ × ℝ → ℂ) (f : CuspStripL2 w Y) :
    (∫ z in hyperbolicCuspStrip w Y,
      inner ℂ (t (z.re, z.im)) (cuspHyperbolicPullback w Y hY f z)) =
      ∫ p, inner ℂ (t p) (f p) ∂cuspStripMeasure w Y := by
  calc
    _ = ∫ z in hyperbolicCuspStrip w Y, inner ℂ (t (z.re, z.im)) (f (z.re, z.im)) := by
      apply integral_congr_ae
      filter_upwards [cuspHyperbolicPullback_ae w Y hY f] with z hz
      rw [hz]
    _ = _ := (cusp_coordinates_measurePreserving w Y hY).integral_comp
      cusp_coordinates_measurableEmbedding (fun p => inner ℂ (t p) (f p))

theorem cuspHyperbolicPullback_pairing_integrable_iff (w Y : ℝ) (hY : 0 < Y)
    (t : ℝ × ℝ → ℂ) (f : CuspStripL2 w Y) :
    IntegrableOn (fun z : UpperHalfPlane =>
      inner ℂ (t (z.re, z.im)) (cuspHyperbolicPullback w Y hY f z))
      (hyperbolicCuspStrip w Y) volume ↔
      Integrable (fun p => inner ℂ (t p) (f p)) (cuspStripMeasure w Y) := by
  have he : (fun z : UpperHalfPlane =>
      inner ℂ (t (z.re, z.im)) (cuspHyperbolicPullback w Y hY f z))
      =ᵐ[volume.restrict (hyperbolicCuspStrip w Y)]
      (fun z => inner ℂ (t (z.re, z.im)) (f (z.re, z.im))) := by
    filter_upwards [cuspHyperbolicPullback_ae w Y hY f] with z hz
    rw [hz]
  exact (integrable_congr he).trans
    ((cusp_coordinates_measurePreserving w Y hY).integrable_comp_emb
      cusp_coordinates_measurableEmbedding (g := fun p => inner ℂ (t p) (f p)))

theorem cuspHyperbolicTwoCell_separable_pairing {w Y : ℝ} (hw : 0 ≤ w) (hY : 0 < Y)
    (χ η : ℝ → ℝ) (f : CuspStripL2 w Y) :
    (∫ z in hyperbolicCuspStrip (2 * w) Y,
      inner ℂ ((χ z.re * η z.im : ℝ) : ℂ)
        (cuspHyperbolicPullback (2 * w) Y hY (cuspTwoCellExtension hw Y f) z)) =
      ∫ p, (χ p.1 * η p.2) • cuspTwoCellExtension hw Y f p
        ∂cuspStripMeasure (2 * w) Y := by
  rw [cuspHyperbolicPullback_pairing_coordinates (2 * w) Y hY
    (fun p => ((χ p.1 * η p.2 : ℝ) : ℂ))]
  congr 1
  funext p
  simp [RCLike.inner_apply, Complex.real_smul, mul_comm]

theorem gamma0CuspTwoCellMassRestriction_separable_pairing (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (χ η : ℝ → ℝ) (f : Gamma0RegionL2 N) :
    (∫ z in hyperbolicCuspStrip (2 * (N : ℝ)) Y,
      inner ℂ ((χ z.re * η z.im : ℝ) : ℂ)
        (gamma0CuspTwoCellMassRestriction N r Y hY f z)) =
      ∫ p, (χ p.1 * η p.2) • gamma0CuspTwoCellCoordinateRestriction N r Y hY f p
        ∂cuspStripMeasure (2 * (N : ℝ)) Y := by
  exact cuspHyperbolicTwoCell_separable_pairing (Nat.cast_nonneg N) hY χ η
    ((cuspHyperbolicPullback (N : ℝ) Y hY).toContinuousLinearMap.adjoint
      (gamma0CuspMassRestriction N r Y hY f))

end
end ArtinMatthews
