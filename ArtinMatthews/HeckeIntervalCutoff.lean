module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! A concrete smooth interval cutoff in the logarithmic variable.
The transition width remains explicit for quantitative Mellin estimates. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped Topology ContDiff

def heckeLogIntervalProfile (ε u v s : ℝ) : ℂ :=
  (Real.smoothTransition ((s-u)/ε)-Real.smoothTransition ((s-v)/ε) : ℝ)

def heckeLogIntervalCutoff (ε u v y : ℝ) : ℂ :=
  if 0 < y then heckeLogIntervalProfile ε u v (Real.log y) else 0

theorem heckeLogIntervalProfile_smooth (ε u v : ℝ) :
    ContDiff ℝ ∞ (heckeLogIntervalProfile ε u v) := by
  unfold heckeLogIntervalProfile
  apply Complex.ofRealCLM.contDiff.comp
  exact (Real.smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const ε)).sub
    (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const ε))

theorem heckeLogIntervalProfile_zero_left {ε u v s : ℝ}
    (hε : 0 < ε) (huv : u ≤ v) (hs : s ≤ u) :
    heckeLogIntervalProfile ε u v s = 0 := by
  unfold heckeLogIntervalProfile
  rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le),
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le)]
  simp

theorem heckeLogIntervalProfile_zero_right {ε u v s : ℝ}
    (hε : 0 < ε) (huv : u ≤ v) (hs : v+ε ≤ s) :
    heckeLogIntervalProfile ε u v s = 0 := by
  unfold heckeLogIntervalProfile
  rw [Real.smoothTransition.one_of_one_le ((le_div_iff₀ hε).mpr (by linarith)),
    Real.smoothTransition.one_of_one_le ((le_div_iff₀ hε).mpr (by linarith))]
  simp

theorem heckeLogIntervalProfile_support {ε u v : ℝ} (hε : 0 < ε) (huv : u ≤ v) :
    Function.support (heckeLogIntervalProfile ε u v) ⊆ Set.Icc u (v+ε) := by
  intro s hs
  constructor
  · by_contra h
    exact hs (heckeLogIntervalProfile_zero_left hε huv (le_of_not_ge h))
  · by_contra h
    exact hs (heckeLogIntervalProfile_zero_right hε huv (le_of_not_ge h))

theorem heckeLogIntervalProfile_norm_le_one {ε u v : ℝ}
    (hε : 0 < ε) (huv : u ≤ v) (s : ℝ) :
    ‖heckeLogIntervalProfile ε u v s‖ ≤ 1 := by
  have hm : Real.smoothTransition ((s-v)/ε) ≤ Real.smoothTransition ((s-u)/ε) :=
    Real.smoothTransition.monotone ((div_le_div_iff_of_pos_right hε).mpr (by linarith))
  rw [heckeLogIntervalProfile, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hm)]
  linarith [Real.smoothTransition.nonneg ((s-v)/ε), Real.smoothTransition.le_one ((s-u)/ε)]

theorem heckeLogIntervalCutoff_exp (ε u v s : ℝ) :
    heckeLogIntervalCutoff ε u v (Real.exp s) = heckeLogIntervalProfile ε u v s := by
  simp only [heckeLogIntervalCutoff, ite_eq_left (Real.exp_pos s), Real.log_exp]

theorem heckeLogIntervalCutoff_smooth {ε u v : ℝ} (hε : 0 < ε) (huv : u ≤ v) :
    ContDiff ℝ ∞ (heckeLogIntervalCutoff ε u v) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : 0 < y
  · have he : heckeLogIntervalCutoff ε u v =ᶠ[𝓝 y]
        (fun z => heckeLogIntervalProfile ε u v (Real.log z)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hy] with z hz
      exact ite_eq_left hz
    exact ((heckeLogIntervalProfile_smooth ε u v).contDiffAt.comp y
      (Real.contDiffAt_log.mpr hy.ne')).congr_of_eventuallyEq he
  · have hye : y < Real.exp u := (le_of_not_gt hy).trans_lt (Real.exp_pos u)
    have he : heckeLogIntervalCutoff ε u v =ᶠ[𝓝 y] (fun _ => 0) := by
      filter_upwards [isOpen_Iio.mem_nhds hye] with z hz
      by_cases hz0 : 0 < z
      · rw [heckeLogIntervalCutoff, ite_eq_left hz0]
        apply heckeLogIntervalProfile_zero_left hε huv
        have hh := Real.log_lt_log hz0 hz
        simpa only [Real.log_exp] using hh.le
      · exact ite_eq_right hz0
    exact contDiffAt_const.congr_of_eventuallyEq he

theorem heckeLogIntervalCutoff_support {ε u v : ℝ} (hε : 0 < ε) (huv : u ≤ v) :
    Function.support (heckeLogIntervalCutoff ε u v) ⊆ Set.Icc (Real.exp u) (Real.exp (v+ε)) := by
  intro y hy
  have hyp : 0 < y := by
    by_contra h
    exact hy (ite_eq_right h)
  have hp : heckeLogIntervalProfile ε u v (Real.log y) ≠ 0 := by
    change heckeLogIntervalCutoff ε u v y ≠ 0 at hy
    simpa only [heckeLogIntervalCutoff, ite_eq_left hyp] using hy
  have hs := heckeLogIntervalProfile_support hε huv hp
  constructor
  · simpa only [Real.exp_log hyp] using Real.exp_le_exp.mpr hs.1
  · simpa only [Real.exp_log hyp] using Real.exp_le_exp.mpr hs.2

theorem heckeLogIntervalCutoff_uniform_support {ε u v : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ Real.log 2) :
    Function.support (heckeLogIntervalCutoff ε u v) ⊆ Set.Icc 1 (2*Real.exp 1) := by
  intro y hy
  have hs := heckeLogIntervalCutoff_support hε huv hy
  constructor
  · have heu : 1 ≤ Real.exp u := by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hu
    exact heu.trans hs.1
  · apply hs.2.trans
    calc
      _ ≤ Real.exp (Real.log 2+1) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

end ArtinMatthews
