module

public import ArtinMatthews.MarkedMemoryOrphanParameterBounds


set_option backward.privateInPublic true
@[expose] public section

/-! Retain the source moment exponent one half while bounding the
logarithm of its length. This avoids an unnecessary full logarithm
in the finite coordinate-tube budget. -/
namespace ArtinMatthews
noncomputable section

theorem markedPhysical_log_log_sharp {x : ℝ} (hlog : 1 ≤ Real.log x) :
    Real.log (Real.log x) ≤ 5*(Real.log x)^(23/100:ℝ) := by
  have hL : 0 ≤ Real.log x := by linarith
  have h := Real.log_le_rpow_div hL (by norm_num : (0:ℝ)<23/100)
  have hp := Real.rpow_nonneg hL (23/100:ℝ)
  linarith

theorem markedPhysicalMomentLength_exp_sharp {x : ℝ} (hlog : 1 ≤ Real.log x) :
    (markedMemoryMomentLength x:ℝ)+1 ≤ Real.exp (8*(Real.log x)^(23/100:ℝ)) := by
  have hL : 0 < Real.log x := by linarith
  have hn := (markedMemoryMomentLength_sqrt_bound hlog).1
  have hl := Real.log_le_log (by positivity : (0:ℝ)<(markedMemoryMomentLength x:ℝ)+1) hn
  rw [Real.log_mul (by norm_num : (4:ℝ)≠0) (by positivity : (Real.log x)^(1/2:ℝ)≠0),
    Real.log_rpow hL] at hl
  have h4 : Real.log 4 ≤ (4:ℝ) := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]
  have hp : 1 ≤ (Real.log x)^(23/100:ℝ) := Real.one_le_rpow hlog (by norm_num)
  have hll := markedPhysical_log_log_sharp hlog
  apply (Real.log_le_iff_le_exp (by positivity : (0:ℝ)<(markedMemoryMomentLength x:ℝ)+1)).mp
  linarith

end
end ArtinMatthews
