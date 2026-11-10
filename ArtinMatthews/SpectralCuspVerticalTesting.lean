module

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

/-! Bounded compact-test functionals on the genuine weighted vertical L² space.
The representing vector includes the exact y²/w density correction. -/
namespace ArtinMatthews
open MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace
noncomputable section

theorem cuspVerticalMeasure_le_smul_volume {Y : ℝ} (hY : 0 < Y) :
    cuspVerticalMeasure Y ≤ ENNReal.ofReal (Y ^ (-2 : ℤ)) • volume := by
  have h : cuspVerticalMeasure Y ≤
      ENNReal.ofReal (Y ^ (-2 : ℤ)) • volume.restrict (Ioi Y) := by
    rw [cuspVerticalMeasure, ← withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    apply ENNReal.ofReal_le_ofReal
    simp only [zpow_neg, zpow_ofNat]
    apply (inv_le_inv₀ (sq_pos_of_pos (hY.trans hy)) (sq_pos_of_pos hY)).mpr
    change Y < y at hy
    nlinarith
  apply h.trans
  gcongr
  exact Measure.restrict_le_self

theorem cuspVerticalL2Measure_le_smul_volume {w Y : ℝ} (hw : 0 < w) (hY : 0 < Y) :
    (cuspHorizontalMeasure w univ) • cuspVerticalMeasure Y ≤
      ENNReal.ofReal (w * Y ^ (-2 : ℤ)) • volume := by
  rw [cuspHorizontalMeasure_univ, ENNReal.ofReal_mul hw.le, ← smul_smul]
  gcongr
  exact cuspVerticalMeasure_le_smul_volume hY

theorem cuspVerticalL2_memLp_compact {w Y : ℝ} (hw : 0 < w) (hY : 0 < Y)
    {t : ℝ → ℂ} (ht : Continuous t) (htc : HasCompactSupport t) :
    MemLp t 2 ((cuspHorizontalMeasure w univ) • cuspVerticalMeasure Y) :=
  (ht.memLp_of_hasCompactSupport htc (μ := volume)).of_measure_le_smul
    ENNReal.ofReal_ne_top (cuspVerticalL2Measure_le_smul_volume hw hY)

def cuspVerticalL2Pairing {w Y : ℝ} (t : ℝ → ℂ)
    (ht : MemLp t 2 ((cuspHorizontalMeasure w univ) • cuspVerticalMeasure Y)) :
    CuspVerticalL2 w Y →L[ℂ] ℂ :=
  innerSL ℂ (ht.star.toLp (star t))

theorem cuspVerticalL2Pairing_apply {w Y : ℝ} (t : ℝ → ℂ)
    (ht : MemLp t 2 ((cuspHorizontalMeasure w univ) • cuspVerticalMeasure Y))
    (f : CuspVerticalL2 w Y) :
    cuspVerticalL2Pairing t ht f =
      ∫ y, f y * t y ∂((cuspHorizontalMeasure w univ) • cuspVerticalMeasure Y) := by
  change inner ℂ (ht.star.toLp (star t)) f = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ht.star.coeFn_toLp] with y hy
  rw [hy]
  simp only [RCLike.inner_apply, Pi.star_apply, starRingEnd_apply, star_star]

theorem cuspVerticalL2_integrable_complex_density_iff {w Y : ℝ}
    (hw : 0 < w) (hY : 0 < Y) (F : ℝ → ℂ) :
    Integrable F ((cuspHorizontalMeasure w univ) • cuspVerticalMeasure Y) ↔
      IntegrableOn (fun y => (y ^ (-2 : ℤ)) • F y) (Ioi Y) volume := by
  rw [cuspHorizontalMeasure_univ,
    integrable_smul_measure (ne_of_gt (ENNReal.ofReal_pos.mpr hw)) ENNReal.ofReal_ne_top,
    cuspVerticalMeasure, integrable_withDensity_iff_integrable_smul'
      (by fun_prop) (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integrable_congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [ENNReal.toReal_ofReal (zpow_nonneg (hY.trans hy).le (-2 : ℤ))]

theorem cuspVerticalL2_integral_complex_density {w Y : ℝ}
    (hw : 0 < w) (hY : 0 < Y) (F : ℝ → ℂ) :
    (∫ y, F y ∂((cuspHorizontalMeasure w univ) • cuspVerticalMeasure Y)) =
      w • (∫ y in Ioi Y, (y ^ (-2 : ℤ)) • F y) := by
  rw [cuspHorizontalMeasure_univ, integral_smul_measure, ENNReal.toReal_ofReal hw.le,
    cuspVerticalMeasure, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [ENNReal.toReal_ofReal (zpow_nonneg (hY.trans hy).le (-2 : ℤ))]

def cuspVerticalTestVector (w : ℝ) (κ : ℝ → ℝ) (y : ℝ) : ℂ :=
  (y ^ 2 / w * κ y : ℝ)

theorem cuspVerticalTestVector_memLp {w Y : ℝ} (hw : 0 < w) (hY : 0 < Y)
    {κ : ℝ → ℝ} (hκ : Continuous κ) (hκc : HasCompactSupport κ) :
    MemLp (cuspVerticalTestVector w κ) 2
      ((cuspHorizontalMeasure w univ) • cuspVerticalMeasure Y) := by
  apply cuspVerticalL2_memLp_compact hw hY
  · unfold cuspVerticalTestVector
    fun_prop
  · exact (hκc.mul_left (f := fun y => y ^ 2 / w)).comp_left (g := Complex.ofReal) (by simp)

/-- The actual Lebesgue compact-test integral, realized as a continuous linear map. -/
def cuspVerticalCompactTest {w Y : ℝ} (hw : 0 < w) (hY : 0 < Y)
    (κ : ℝ → ℝ) (hκ : Continuous κ) (hκc : HasCompactSupport κ) :
    CuspVerticalL2 w Y →L[ℂ] ℂ :=
  cuspVerticalL2Pairing (cuspVerticalTestVector w κ)
    (cuspVerticalTestVector_memLp hw hY hκ hκc)

theorem cuspVerticalTestVector_density {w y : ℝ} (hw : w ≠ 0) (hy : y ≠ 0)
    (κ : ℝ → ℝ) (z : ℂ) :
    w • ((y ^ (-2 : ℤ)) • (z * cuspVerticalTestVector w κ y)) = κ y • z := by
  simp only [cuspVerticalTestVector, zpow_neg, zpow_ofNat, Complex.real_smul,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_inv]
  field_simp [Complex.ofReal_ne_zero.mpr hw, Complex.ofReal_ne_zero.mpr hy]

theorem cuspVerticalCompactTest_integrable {w Y : ℝ} (hw : 0 < w) (hY : 0 < Y)
    (κ : ℝ → ℝ) (hκ : Continuous κ) (hκc : HasCompactSupport κ)
    (f : CuspVerticalL2 w Y) :
    IntegrableOn (fun y => κ y • f y) (Ioi Y) volume := by
  have ht := cuspVerticalTestVector_memLp hw hY hκ hκc
  have hi := (cuspVerticalL2_integrable_complex_density_iff hw hY _).mp
    ((Lp.memLp f).integrable_mul ht)
  apply (hi.smul w).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact cuspVerticalTestVector_density hw.ne' (hY.trans hy).ne' κ (f y)

theorem cuspVerticalCompactTest_apply {w Y : ℝ} (hw : 0 < w) (hY : 0 < Y)
    (κ : ℝ → ℝ) (hκ : Continuous κ) (hκc : HasCompactSupport κ)
    (f : CuspVerticalL2 w Y) :
    cuspVerticalCompactTest hw hY κ hκ hκc f = ∫ y in Ioi Y, κ y • f y := by
  rw [cuspVerticalCompactTest, cuspVerticalL2Pairing_apply,
    cuspVerticalL2_integral_complex_density hw hY, ← integral_smul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact cuspVerticalTestVector_density hw.ne' (hY.trans hy).ne' κ (f y)

end
end ArtinMatthews
