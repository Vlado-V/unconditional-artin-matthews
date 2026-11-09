module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Tactic.NormNum


set_option backward.privateInPublic true
@[expose] public section

/-! A fixed real Schwartz cutoff for the original determinant comparison.
Its plateau contains every surviving value of (b-a)/Y. -/
namespace ArtinMatthews
open Set
open scoped ContDiff
noncomputable section

private def markedTypeIIDeterminantBump : ContDiffBump (0:ℝ) :=
  ⟨4,5,by norm_num,by norm_num⟩

private def markedTypeIIDeterminantCutoffFun (t : ℝ) : ℂ :=
  (markedTypeIIDeterminantBump t : ℂ)

private theorem markedTypeIIDeterminantCutoffFun_support :
    Function.support markedTypeIIDeterminantCutoffFun ⊆ Icc (-5:ℝ) 5 := by
  intro t ht
  have h : t ∈ Function.support markedTypeIIDeterminantBump :=
    Complex.ofReal_ne_zero.mp ht
  rw [markedTypeIIDeterminantBump.support_eq,Metric.mem_ball,Real.dist_eq,sub_zero] at h
  change |t| < 5 at h
  exact abs_le.mp h.le

def markedTypeIIDeterminantCutoff : SchwartzMap ℝ ℂ :=
  (HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    markedTypeIIDeterminantCutoffFun_support).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp markedTypeIIDeterminantBump.contDiff)

theorem markedTypeIIDeterminantCutoff_one (t : ℝ) (ht : t ∈ Icc (-4:ℝ) 4) :
    markedTypeIIDeterminantCutoff t=1 := by
  have hb : markedTypeIIDeterminantBump t=1 := by
    apply markedTypeIIDeterminantBump.one_of_mem_closedBall
    rw [Metric.mem_closedBall,Real.dist_eq,sub_zero]
    exact abs_le.mpr ht
  change (markedTypeIIDeterminantBump t:ℂ)=1
  rw [hb,Complex.ofReal_one]

theorem markedTypeIIDeterminantCutoff_support :
    Function.support markedTypeIIDeterminantCutoff ⊆ Icc (-5:ℝ) 5 :=
  markedTypeIIDeterminantCutoffFun_support

theorem markedTypeIIDeterminantCutoff_tsupport :
    tsupport markedTypeIIDeterminantCutoff ⊆ Icc (-5:ℝ) 5 :=
  closure_minimal markedTypeIIDeterminantCutoff_support isClosed_Icc

theorem markedTypeIIDeterminantCutoff_norm_le_one (t : ℝ) :
    ‖markedTypeIIDeterminantCutoff t‖≤1 := by
  change ‖(markedTypeIIDeterminantBump t:ℂ)‖≤1
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg markedTypeIIDeterminantBump.nonneg]
  exact markedTypeIIDeterminantBump.le_one

theorem markedTypeIIDeterminantCutoff_real (t : ℝ) :
    star (markedTypeIIDeterminantCutoff t)=markedTypeIIDeterminantCutoff t :=
  Complex.conj_ofReal _

end
end ArtinMatthews
