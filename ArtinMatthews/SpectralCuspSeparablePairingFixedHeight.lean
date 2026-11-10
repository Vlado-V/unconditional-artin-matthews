module

public import ArtinMatthews.SpectralCuspTwoCellOperator
public import ArtinMatthews.SpectralHorizontalPeriodPartition
public import Mathlib.Analysis.CStarAlgebra.Classes
public import ArtinMatthews.CuspAverageProjectionIntegral
public import ArtinMatthews.SpectralCuspSeparablePairingBase
public import ArtinMatthews.SpectralCuspTwoCellTesting
public import ArtinMatthews.SpectralCuspVerticalTesting
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


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
