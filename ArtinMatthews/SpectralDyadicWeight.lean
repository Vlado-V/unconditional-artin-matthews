module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Pow.Real


set_option backward.privateInPublic true
@[expose] public section

/-! A literal smooth [1,2]-supported weight for two interlaced dyadic
families. The overlap prevents the endpoint gap of a single such family. -/
namespace ArtinMatthews

open Set
open scoped ContDiff
noncomputable section

def spectralDyadicRatio : ℝ := Real.sqrt 2

lemma spectralDyadicRatio_sq : spectralDyadicRatio^2 = 2 :=
  Real.sq_sqrt (by norm_num)

lemma spectralDyadicRatio_one_lt : 1 < spectralDyadicRatio := by
  have h := Real.sqrt_nonneg (2 : ℝ)
  have h' := spectralDyadicRatio_sq
  change 0 ≤ spectralDyadicRatio at h
  nlinarith

lemma spectralDyadicRatio_pos : 0 < spectralDyadicRatio :=
  zero_lt_one.trans spectralDyadicRatio_one_lt

def spectralDyadicStep (x : ℝ) : ℝ :=
  Real.smoothTransition ((x-1)/(spectralDyadicRatio-1))

def spectralDyadicWeight (x : ℝ) : ℝ :=
  spectralDyadicStep x - spectralDyadicStep (x/spectralDyadicRatio)

lemma spectralDyadicStep_zero {x : ℝ} (hx : x ≤ 1) : spectralDyadicStep x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (by linarith)
    (sub_nonneg.mpr spectralDyadicRatio_one_lt.le)

lemma spectralDyadicStep_one {x : ℝ} (hx : spectralDyadicRatio ≤ x) :
    spectralDyadicStep x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  apply (le_div_iff₀ (sub_pos.mpr spectralDyadicRatio_one_lt)).2
  linarith

lemma spectralDyadicStep_monotone : Monotone spectralDyadicStep := by
  intro x y hxy
  apply Real.smoothTransition.monotone
  exact div_le_div_of_nonneg_right (by linarith) (sub_nonneg.mpr spectralDyadicRatio_one_lt.le)

lemma spectralDyadicWeight_zero_of_le_one {x : ℝ} (hx : x ≤ 1) :
    spectralDyadicWeight x = 0 := by
  unfold spectralDyadicWeight
  rw [spectralDyadicStep_zero hx,spectralDyadicStep_zero]
  · ring
  · exact (div_le_one spectralDyadicRatio_pos).2 (hx.trans spectralDyadicRatio_one_lt.le)

lemma spectralDyadicWeight_zero_of_two_le {x : ℝ} (hx : 2 ≤ x) :
    spectralDyadicWeight x = 0 := by
  have hr := spectralDyadicRatio_sq
  have hp := spectralDyadicRatio_pos
  have hs : spectralDyadicRatio ≤ x/spectralDyadicRatio := by
    apply (le_div_iff₀ hp).2
    nlinarith
  have hx' : spectralDyadicRatio ≤ x := by nlinarith [spectralDyadicRatio_one_lt]
  unfold spectralDyadicWeight
  rw [spectralDyadicStep_one hx',spectralDyadicStep_one hs]
  ring

lemma spectralDyadicWeight_nonneg (x : ℝ) : 0 ≤ spectralDyadicWeight x := by
  by_cases hx : x ≤ 1
  · rw [spectralDyadicWeight_zero_of_le_one hx]
  · have hxpos : 0 ≤ x := by linarith
    apply sub_nonneg.mpr
    apply spectralDyadicStep_monotone
    exact (div_le_self hxpos spectralDyadicRatio_one_lt.le)

lemma spectralDyadicWeight_le_one (x : ℝ) : spectralDyadicWeight x ≤ 1 := by
  have h₁ := Real.smoothTransition.le_one ((x-1)/(spectralDyadicRatio-1))
  have h₂ := Real.smoothTransition.nonneg ((x/spectralDyadicRatio-1)/(spectralDyadicRatio-1))
  unfold spectralDyadicWeight spectralDyadicStep
  linarith

lemma spectralDyadicWeight_support :
    Function.support spectralDyadicWeight ⊆ Icc (1 : ℝ) 2 := by
  intro x hx
  have hn : spectralDyadicWeight x ≠ 0 := hx
  constructor
  · by_contra h
    exact hn (spectralDyadicWeight_zero_of_le_one (le_of_lt (lt_of_not_ge h)))
  · by_contra h
    exact hn (spectralDyadicWeight_zero_of_two_le (le_of_lt (lt_of_not_ge h)))

lemma spectralDyadicWeight_contDiff : ContDiff ℝ ∞ spectralDyadicWeight := by
  unfold spectralDyadicWeight spectralDyadicStep
  fun_prop

lemma spectralDyadicWeight_hasCompactSupport : HasCompactSupport spectralDyadicWeight := by
  exact (isCompact_Icc : IsCompact (Icc (1 : ℝ) 2)).of_isClosed_subset
    (isClosed_tsupport _) (closure_minimal spectralDyadicWeight_support isClosed_Icc)

lemma spectralDyadicWeight_ratio : spectralDyadicWeight spectralDyadicRatio = 1 := by
  unfold spectralDyadicWeight
  rw [spectralDyadicStep_one le_rfl,div_self spectralDyadicRatio_pos.ne',spectralDyadicStep_zero le_rfl]
  norm_num

end
end ArtinMatthews
