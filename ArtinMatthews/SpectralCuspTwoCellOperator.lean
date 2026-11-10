module

public import ArtinMatthews.SpectralCuspTwoCellMeasure
public import ArtinMatthews.CuspAverageProjectionOperator
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


set_option backward.privateInPublic true
@[expose] public section

/-! A bounded literal two-cell extension of arbitrary completed period-strip
L² vectors.  Representatives are folded, without assuming their continuity. -/
namespace ArtinMatthews
open MeasureTheory Set Filter
open scoped ENNReal
noncomputable section

def cuspTwoCellExtension {w : ℝ} (hw : 0 ≤ w) (Y : ℝ) :
    CuspStripL2 w Y →L[ℝ] CuspStripL2 (2 * w) Y :=
  (Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := 2) ℝ (spectralTwoCellCoordinateFold w)
    (spectralTwoCellCoordinateFold_preserving hw Y)).toContinuousLinearMap.comp
      (Lp.LpToLpOfMeasureLeSMul (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
        (le_refl ((2 : ℝ≥0∞) • cuspStripMeasure w Y)))

theorem cuspTwoCellExtension_norm_le {w : ℝ} (hw : 0 ≤ w) (Y : ℝ) :
    ‖cuspTwoCellExtension hw Y‖ ≤ Real.sqrt 2 := by
  let S : CuspStripL2 w Y →L[ℝ] Lp ℂ 2 ((2 : ℝ≥0∞) • cuspStripMeasure w Y) :=
    Lp.LpToLpOfMeasureLeSMul (by norm_num : (2 : ℝ≥0∞) ≠ ∞) le_rfl
  let U := (Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := 2) ℝ (spectralTwoCellCoordinateFold w)
    (spectralTwoCellCoordinateFold_preserving hw Y))
  have hU : ‖U.toContinuousLinearMap‖ ≤ 1 := U.norm_toContinuousLinearMap_le
  have hS : ‖S‖ ≤ Real.sqrt 2 := by
    have h := Lp.norm_LpToLpOfMeasureLeSMul_le (E := ℂ) (p := 2)
      (μ := (2 : ℝ≥0∞) • cuspStripMeasure w Y) (ν := cuspStripMeasure w Y)
      (c := (2 : ℝ≥0∞)) (by norm_num) le_rfl
    simpa only [ENNReal.toReal_ofNat, ENNReal.toReal_div, ENNReal.toReal_one,
      Real.sqrt_eq_rpow] using h
  change ‖U.toContinuousLinearMap.comp S‖ ≤ _
  calc
    _ ≤ ‖U.toContinuousLinearMap‖ * ‖S‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * Real.sqrt 2 := mul_le_mul hU hS (norm_nonneg _) (by norm_num)
    _ = _ := one_mul _

theorem cuspTwoCellExtension_norm_apply_le {w : ℝ} (hw : 0 ≤ w) (Y : ℝ)
    (f : CuspStripL2 w Y) :
    ‖cuspTwoCellExtension hw Y f‖ ≤ Real.sqrt 2 * ‖f‖ :=
  ((cuspTwoCellExtension hw Y).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right (cuspTwoCellExtension_norm_le hw Y) (norm_nonneg _))

theorem cuspTwoCellExtension_ae {w : ℝ} (hw : 0 ≤ w) (Y : ℝ) (f : CuspStripL2 w Y) :
    cuspTwoCellExtension hw Y f =ᵐ[cuspStripMeasure (2 * w) Y]
      fun z => f (spectralTwoCellCoordinateFold w z) := by
  let S : CuspStripL2 w Y →L[ℝ] Lp ℂ 2 ((2 : ℝ≥0∞) • cuspStripMeasure w Y) :=
    Lp.LpToLpOfMeasureLeSMul (by norm_num : (2 : ℝ≥0∞) ≠ ∞) le_rfl
  have hS : S f =ᵐ[(2 : ℝ≥0∞) • cuspStripMeasure w Y] f :=
    Lp.coeFn_LpToLpOfMeasureLeSMul (by norm_num) le_rfl f
  exact (Lp.coeFn_compMeasurePreserving (S f) (spectralTwoCellCoordinateFold_preserving hw Y)).trans
    ((spectralTwoCellCoordinateFold_preserving hw Y).quasiMeasurePreserving.ae_eq_comp hS)

end
end ArtinMatthews
