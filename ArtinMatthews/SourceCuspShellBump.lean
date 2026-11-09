module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Normed.Group.Bounded


set_option backward.privateInPublic true
@[expose] public section

/-! One fixed smooth logarithmic cutoff for three consecutive dyadic cusp shells. -/
namespace ArtinMatthews
open Set
open scoped ContDiff
noncomputable section

def sourceCuspShellBump (t : ℝ) : ℝ :=
  Real.smoothTransition (t / Real.log 2) * Real.smoothTransition (3 - t / Real.log 2)

theorem sourceCuspShellBump_contDiff : ContDiff ℝ ∞ sourceCuspShellBump :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.div_const _)).mul
    (Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_id.div_const _)))

theorem sourceCuspShellBump_nonneg (t : ℝ) : 0 ≤ sourceCuspShellBump t :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem sourceCuspShellBump_le_one (t : ℝ) : sourceCuspShellBump t ≤ 1 := by
  exact (mul_le_mul (Real.smoothTransition.le_one _) (Real.smoothTransition.le_one _)
    (Real.smoothTransition.nonneg _) (by norm_num)).trans_eq (one_mul 1)

theorem sourceCuspShellBump_zero_left {t : ℝ} (ht : t ≤ 0) : sourceCuspShellBump t = 0 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold sourceCuspShellBump
  rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg ht hlog.le), zero_mul]

theorem sourceCuspShellBump_zero_right {t : ℝ} (ht : 3 * Real.log 2 ≤ t) :
    sourceCuspShellBump t = 0 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h : 3 ≤ t / Real.log 2 := (le_div_iff₀ hlog).mpr ht
  unfold sourceCuspShellBump
  rw [Real.smoothTransition.zero_of_nonpos (by linarith : 3 - t / Real.log 2 ≤ 0), mul_zero]

theorem sourceCuspShellBump_one {t : ℝ} (hlo : Real.log 2 ≤ t) (hhi : t ≤ 2 * Real.log 2) :
    sourceCuspShellBump t = 1 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h₁ : 1 ≤ t / Real.log 2 := (le_div_iff₀ hlog).mpr (by simpa only [one_mul] using hlo)
  have h₂ : t / Real.log 2 ≤ 2 := (div_le_iff₀ hlog).mpr hhi
  unfold sourceCuspShellBump
  rw [Real.smoothTransition.one_of_one_le h₁,
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 3 - t / Real.log 2), one_mul]

theorem sourceCuspShellBump_tsupport : tsupport sourceCuspShellBump ⊆ Icc 0 (3 * Real.log 2) := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  constructor
  · by_contra h
    exact ht (sourceCuspShellBump_zero_left (le_of_not_ge h))
  · by_contra h
    exact ht (sourceCuspShellBump_zero_right (le_of_not_ge h))

theorem sourceCuspShellBump_hasCompactSupport : HasCompactSupport sourceCuspShellBump :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) sourceCuspShellBump_tsupport

theorem sourceCuspShellBump_deriv_bound : ∃ B : ℝ, 0 < B ∧ ∀ t, ‖deriv sourceCuspShellBump t‖ ≤ B := by
  obtain ⟨B, hB⟩ :=
    (sourceCuspShellBump_contDiff.continuous_deriv (by norm_num)).bounded_above_of_compact_support
      sourceCuspShellBump_hasCompactSupport.deriv
  exact ⟨max 1 B, lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    fun t => (hB t).trans (le_max_right _ _)⟩

end
end ArtinMatthews
