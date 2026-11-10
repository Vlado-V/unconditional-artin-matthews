module

public import ArtinMatthews.CuspAverageProjectionOperator
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
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

/-! Local Lebesgue integrability of the actual weighted vertical L² classes.
The comparison is proved on bounded intervals, where the literal hyperbolic density
has a positive lower bound; no unweighted integrability premise is used. -/
namespace ArtinMatthews
open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section

/-- On a bounded positive interval the actual hyperbolic vertical measure dominates
Lebesgue measure with the explicit upper-height-squared factor. -/
theorem cuspVerticalMeasure_interval_le {Y a b : ℝ} (hY : 0 < Y) (ha : Y < a) :
    volume.restrict (Icc a b) ≤ ENNReal.ofReal (b ^ 2) • cuspVerticalMeasure Y := by
  have hs : Icc a b ⊆ Ioi Y := fun _ hx => ha.trans_le hx.1
  have hrestrict : (cuspVerticalMeasure Y).restrict (Icc a b) =
      (volume.restrict (Icc a b)).withDensity
        (fun y : ℝ => ENNReal.ofReal (y ^ (-2 : ℤ))) := by
    rw [cuspVerticalMeasure, restrict_withDensity measurableSet_Icc,
      Measure.restrict_restrict_of_subset hs]
  have hcomp : volume.restrict (Icc a b) ≤
      ENNReal.ofReal (b ^ 2) • (cuspVerticalMeasure Y).restrict (Icc a b) := by
    rw [hrestrict, ← withDensity_smul _ (by fun_prop)]
    conv_lhs => rw [← one_smul ℝ≥0∞ (volume.restrict (Icc a b)), ← withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    have hypos : 0 < y := hY.trans (ha.trans_le hy.1)
    have hbpos : 0 < b := hypos.trans_le hy.2
    have hsq : y ^ 2 ≤ b ^ 2 := by nlinarith [hy.2]
    have hreal : 1 ≤ b ^ 2 * y ^ (-2 : ℤ) := by
      rw [zpow_neg, zpow_ofNat, ← div_eq_mul_inv]
      exact (one_le_div (sq_pos_of_pos hypos)).mpr hsq
    change 1 ≤ ENNReal.ofReal (b ^ 2) * ENNReal.ofReal (y ^ (-2 : ℤ))
    rw [← ENNReal.ofReal_mul (sq_nonneg b)]
    exact_mod_cast ENNReal.ofReal_le_ofReal hreal
  apply hcomp.trans
  gcongr
  exact Measure.restrict_le_self

/-- The horizontal mass normalization is retained in the local comparison. -/
theorem cuspVerticalL2Measure_interval_le {w Y a b : ℝ} (hw : 0 < w)
    (hY : 0 < Y) (ha : Y < a) :
    volume.restrict (Icc a b) ≤ ENNReal.ofReal (b ^ 2 / w) •
      ((cuspHorizontalMeasure w univ) • cuspVerticalMeasure Y) := by
  rw [cuspHorizontalMeasure_univ, smul_smul,
    ← ENNReal.ofReal_mul (div_nonneg (sq_nonneg b) hw.le), div_mul_cancel₀ _ hw.ne']
  exact cuspVerticalMeasure_interval_le hY ha

/-- Actual weighted vertical L² classes are Lebesgue integrable on each compact positive interval
lying above the defining cusp height. -/
theorem cuspVerticalL2_integrableOn_Icc (w Y : ℝ) (hw : 0 < w) (hY : 0 < Y)
    (f : CuspVerticalL2 w Y) {a b : ℝ} (ha : Y < a) :
    IntegrableOn (f : ℝ → ℂ) (Icc a b) volume := by
  have hm : MemLp (f : ℝ → ℂ) 2 (volume.restrict (Icc a b)) :=
    (Lp.memLp f).of_measure_le_smul ENNReal.ofReal_ne_top
      (cuspVerticalL2Measure_interval_le hw hY ha)
  exact hm.integrable (by norm_num)

/-- A genuine completed weighted vertical L² class has a locally Lebesgue L¹ representative
throughout its positive-height strip. -/
theorem cuspVerticalL2_locallyIntegrableOn (w Y : ℝ) (hw : 0 < w) (hY : 0 < Y)
    (f : CuspVerticalL2 w Y) :
    LocallyIntegrableOn (f : ℝ → ℂ) (Ioi Y) volume := by
  intro x hx
  change Y < x at hx
  refine ⟨Icc ((Y + x) / 2) (x + 1), ?_,
    cuspVerticalL2_integrableOn_Icc w Y hw hY f (by linarith)⟩
  exact mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds (by linarith) (by linarith))

end
end ArtinMatthews
