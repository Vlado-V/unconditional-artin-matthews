module

public import ArtinMatthews.SpectralCuspSeparablePairingBase
public import ArtinMatthews.CuspAverageProjectionIntegral


set_option backward.privateInPublic true
@[expose] public section

/-! Exact compact-test evaluations on the genuine folded two-cell field.
The horizontal partition extracts its actual Hilbert adjoint constant term;
the second horizontal derivative contributes zero. -/
namespace ArtinMatthews
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal ContDiff

 theorem cuspTwoCell_partition_pairing {w Y : ℝ} (hw : 0 < w) (hY : 0 < Y)
    (η : ℝ → ℝ) (hη : Continuous η) (hcη : HasCompactSupport η)
    (f : CuspStripL2 w Y) :
    (∫ p : ℝ × ℝ, (spectralHorizontalPartition w p.1 * η p.2) •
      cuspTwoCellExtension hw.le Y f p ∂cuspStripMeasure (2 * w) Y) =
      w • (∫ y in Ioi Y, (η y / y ^ 2) •
        ((cuspVerticalPullback w Y).toContinuousLinearMap.adjoint f) y) := by
  rw [cuspSeparable_twoCell_Fubini hw hY _ η
    (spectralHorizontalPartition_contDiff w).continuous hη
    (spectralHorizontalPartition_hasCompactSupport hw) hcη
    (spectralHorizontalPartition_tsupport hw)]
  have hm := cuspVerticalAdjoint_ae_horizontalMean w Y hw f
  calc
    _ = ∫ y, η y • (w • ((cuspVerticalPullback w Y).toContinuousLinearMap.adjoint f) y)
        ∂cuspVerticalMeasure Y := by
      apply integral_congr_ae
      filter_upwards [cuspTwoCellExtension_weighted_integral_ae hw Y f, hm] with y hy hmy
      rw [hy, hmy]
      congr 1
      simp only [cuspHorizontalMean, Complex.real_smul]
      rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hw.ne'), one_mul]
    _ = w • ∫ y, η y • ((cuspVerticalPullback w Y).toContinuousLinearMap.adjoint f) y
        ∂cuspVerticalMeasure Y := by
      rw [← integral_smul]
      apply integral_congr_ae
      exact Eventually.of_forall fun y => smul_comm (η y) w _
    _ = ∫ y, η y • ((cuspVerticalPullback w Y).toContinuousLinearMap.adjoint f) y
        ∂((cuspHorizontalMeasure w univ) • cuspVerticalMeasure Y) := by
      rw [integral_smul_measure]
      simp only [cuspHorizontalMeasure_univ, ENNReal.toReal_ofReal hw.le]
    _ = _ := by
      rw [cuspVerticalL2_integral_complex_density hw hY]
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by
        simp only [smul_smul, zpow_neg, zpow_ofNat, div_eq_mul_inv]
        rw [mul_comm]

 theorem cuspTwoCell_partition_deriv2_pairing {w Y : ℝ} (hw : 0 < w) (hY : 0 < Y)
    (η : ℝ → ℝ) (hη : Continuous η) (hcη : HasCompactSupport η)
    (f : CuspStripL2 w Y) :
    (∫ p : ℝ × ℝ, (deriv (deriv (spectralHorizontalPartition w)) p.1 * η p.2) •
      cuspTwoCellExtension hw.le Y f p ∂cuspStripMeasure (2 * w) Y) = 0 := by
  have hd := (contDiff_infty_iff_deriv.mp (spectralHorizontalPartition_contDiff w)).2
  have hdd := (contDiff_infty_iff_deriv.mp hd).2
  rw [cuspSeparable_twoCell_Fubini hw hY _ η hdd.continuous hη
    (spectralHorizontalPartition_hasCompactSupport hw).deriv.deriv hcη
    (tsupport_deriv_subset.trans
      (tsupport_deriv_subset.trans (spectralHorizontalPartition_tsupport hw)))]
  apply integral_eq_zero_of_ae
  filter_upwards [cuspTwoCellExtension_period_fiber_ae hw Y f] with y hy
  change η y • (∫ x, deriv (deriv (spectralHorizontalPartition w)) x •
    cuspTwoCellExtension hw.le Y f (x, y)) = (0 : ℂ)
  rw [hy.2.2.2.2.2, smul_zero]

end
end ArtinMatthews
