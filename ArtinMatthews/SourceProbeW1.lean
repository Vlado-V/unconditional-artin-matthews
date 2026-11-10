module

public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct


set_option backward.privateInPublic true
@[expose] public section

/-! The auxiliary positive smooth probe weight, normalized to have integral one. -/

namespace ArtinMatthews.SourcePhysical
open Function Set MeasureTheory
open scoped ContDiff
noncomputable section

private def probeW1Bump : ContDiffBump (2 : ℝ) where
  rIn := 1 / 4
  rOut := 1 / 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- A positive smooth weight with support closure contained in the positive line. -/
def sourceProbeW1 : ℝ → ℝ := probeW1Bump.normed volume

def sourceProbeW1Complex (t : ℝ) : ℂ := (sourceProbeW1 t : ℂ)

theorem sourceProbeW1_nonneg (t : ℝ) : 0 ≤ sourceProbeW1 t :=
  probeW1Bump.nonneg_normed t

theorem sourceProbeW1_support : support sourceProbeW1 = Ioo (3 / 2 : ℝ) (5 / 2) := by
  rw [sourceProbeW1, probeW1Bump.support_normed_eq, Real.ball_eq_Ioo]
  norm_num [probeW1Bump]

theorem sourceProbeW1_tsupport : tsupport sourceProbeW1 = Icc (3 / 2 : ℝ) (5 / 2) := by
  rw [sourceProbeW1, probeW1Bump.tsupport_normed_eq, Real.closedBall_eq_Icc]
  norm_num [probeW1Bump]

theorem sourceProbeW1_pos {t : ℝ} (ht : t ∈ Ioo (3 / 2 : ℝ) (5 / 2)) :
    0 < sourceProbeW1 t := by
  have h : t ∈ support sourceProbeW1 := sourceProbeW1_support.symm ▸ ht
  exact (sourceProbeW1_nonneg t).lt_of_ne' (mem_support.mp h)

theorem sourceProbeW1_ne_zero : sourceProbeW1 ≠ 0 := by
  intro h
  have hp := sourceProbeW1_pos (t := 2) (by norm_num)
  have hz := congrFun h 2
  exact hp.ne' hz

theorem sourceProbeW1_contDiff : ContDiff ℝ ∞ sourceProbeW1 :=
  probeW1Bump.contDiff_normed

theorem sourceProbeW1Complex_contDiff : ContDiff ℝ ∞ sourceProbeW1Complex :=
  Complex.ofRealCLM.contDiff.comp sourceProbeW1_contDiff

theorem sourceProbeW1Complex_tsupport : tsupport sourceProbeW1Complex = Icc (3 / 2 : ℝ) (5 / 2) := by
  have h : support sourceProbeW1Complex = support sourceProbeW1 := by
    ext t
    simp [sourceProbeW1Complex, mem_support]
  exact (congrArg closure h).trans sourceProbeW1_tsupport

theorem sourceProbeW1Complex_compact : HasCompactSupport sourceProbeW1Complex := by
  rw [HasCompactSupport, sourceProbeW1Complex_tsupport]
  exact isCompact_Icc

theorem sourceProbeW1Complex_positive_support : tsupport sourceProbeW1Complex ⊆ Ioi 0 := by
  rw [sourceProbeW1Complex_tsupport]
  exact fun _ ht => (by norm_num : (0 : ℝ) < 3 / 2).trans_le ht.1

theorem sourceProbeW1_integral_positiveLine : (∫ t : ℝ in Ioi 0, sourceProbeW1 t) = 1 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => ?_)]
  · exact probeW1Bump.integral_normed
  · apply notMem_support.mp
    intro h
    rw [sourceProbeW1_support] at h
    exact ht ((by norm_num : (0 : ℝ) < 3 / 2).trans h.1)

end
end ArtinMatthews.SourcePhysical
