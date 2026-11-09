module

public import ArtinMatthews.SpectralCuspTwoCellRepresentative
public import ArtinMatthews.SpectralHorizontalPeriodMeasurableFibers


set_option backward.privateInPublic true
@[expose] public section

/-! Actual compact horizontal testing of every completed period-strip L²
vector, using the bounded doubled representative rather than a smooth proxy. -/
namespace ArtinMatthews
open MeasureTheory Set Filter
noncomputable section

theorem cuspTwoCellExtension_period_fiber_ae {w : ℝ} (hw : 0 < w) (Y : ℝ)
    (f : CuspStripL2 w Y) :
    ∀ᵐ y ∂cuspVerticalMeasure Y,
      spectralHorizontalPeriodFiber w (fun x => cuspTwoCellExtension hw.le Y f (x, y)) :=
  spectralHorizontalPeriodFiber_ae_of_cusp_memLp hw (Lp.memLp _)
    (cuspTwoCellExtension_shift_ae hw.le Y f)

theorem cuspTwoCellExtension_weighted_integral_ae {w : ℝ} (hw : 0 < w) (Y : ℝ)
    (f : CuspStripL2 w Y) :
    ∀ᵐ y ∂cuspVerticalMeasure Y,
      (∫ x, spectralHorizontalPartition w x • cuspTwoCellExtension hw.le Y f (x, y)) =
        ∫ x in Ioc 0 w, f (x, y) := by
  have hs := (Measure.measurePreserving_swap (μ := cuspVerticalMeasure Y)
    (ν := cuspHorizontalMeasure w)).quasiMeasurePreserving.ae_eq_comp
      (cuspTwoCellExtension_first_ae hw.le Y f)
  have hxy := Measure.ae_ae_of_ae_prod hs
  filter_upwards [cuspTwoCellExtension_period_fiber_ae hw Y f, hxy] with y hy hxy
  calc
    _ = ∫ x in 0..w, cuspTwoCellExtension hw.le Y f (x, y) := hy.2.2.2.1
    _ = _ := by
      rw [intervalIntegral.integral_of_le hw.le]
      exact integral_congr_ae hxy

theorem cuspTwoCellExtension_weighted_integral_ae_volume {w Y : ℝ}
    (hw : 0 < w) (hY : 0 < Y) (f : CuspStripL2 w Y) :
    ∀ᵐ y ∂volume.restrict (Ioi Y),
      (∫ x, spectralHorizontalPartition w x • cuspTwoCellExtension hw.le Y f (x, y)) =
        ∫ x in Ioc 0 w, f (x, y) :=
  (spectralHorizontal_cuspVertical_ae_iff hY).mp
    (cuspTwoCellExtension_weighted_integral_ae hw Y f)

theorem cuspTwoCellExtension_derivative_integrals_ae_volume {w Y : ℝ}
    (hw : 0 < w) (hY : 0 < Y) (f : CuspStripL2 w Y) :
    ∀ᵐ y ∂volume.restrict (Ioi Y),
      (∫ x, deriv (spectralHorizontalPartition w) x • cuspTwoCellExtension hw.le Y f (x, y)) = 0 ∧
      (∫ x, deriv (deriv (spectralHorizontalPartition w)) x •
        cuspTwoCellExtension hw.le Y f (x, y)) = 0 := by
  apply (spectralHorizontal_cuspVertical_ae_iff hY).mp
  filter_upwards [cuspTwoCellExtension_period_fiber_ae hw Y f] with y hy
  exact hy.2.2.2.2

end
end ArtinMatthews
