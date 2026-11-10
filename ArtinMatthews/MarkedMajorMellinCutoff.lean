module

public import ArtinMatthews.MarkedMajorMellinKernelSeparation
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set
open scoped ContDiff
noncomputable section

def majorMellinPositiveBump (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ContDiffBump ((a+b)/2) where
  rIn := (b-a)/2
  rOut := b/2
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

def majorMellinPositiveCutoffFun (a b : ℝ) (ha : 0 < a) (hab : a < b) (x : ℝ) : ℂ :=
  (majorMellinPositiveBump a b ha hab x : ℂ)

theorem majorMellinPositiveCutoffFun_contDiff (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ContDiff ℝ ∞ (majorMellinPositiveCutoffFun a b ha hab) :=
  Complex.ofRealCLM.contDiff.comp (majorMellinPositiveBump a b ha hab).contDiff

theorem majorMellinPositiveCutoffFun_plateau (a b : ℝ) (ha : 0 < a) (hab : a < b)
    {x : ℝ} (hx : x ∈ Icc a b) : majorMellinPositiveCutoffFun a b ha hab x = 1 := by
  have h : majorMellinPositiveBump a b ha hab x = 1 := by
    apply (majorMellinPositiveBump a b ha hab).one_of_mem_closedBall
    rw [Metric.mem_closedBall,Real.dist_eq]
    change |x-(a+b)/2| ≤ (b-a)/2
    exact abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩
  simp only [majorMellinPositiveCutoffFun,h,Complex.ofReal_one]

theorem majorMellinPositiveCutoffFun_tsupport (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    tsupport (majorMellinPositiveCutoffFun a b ha hab) ⊆ Icc (a/2) (b+a/2) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have hn : majorMellinPositiveBump a b ha hab x ≠ 0 := Complex.ofReal_ne_zero.mp hx
  have hball : x ∈ Metric.ball ((a+b)/2) (b/2) := by
    change x ∈ Metric.ball ((a+b)/2) (majorMellinPositiveBump a b ha hab).rOut
    rw [← (majorMellinPositiveBump a b ha hab).support_eq]
    exact hn
  rw [Metric.mem_ball,Real.dist_eq,abs_lt] at hball
  exact ⟨by linarith [hball.1],by linarith [hball.2]⟩

def majorMellinPositiveCutoff (a b : ℝ) (ha : 0 < a) (hab : a < b) : SchwartzMap ℝ ℂ := by
  have h : HasCompactSupport (majorMellinPositiveCutoffFun a b ha hab) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
      (majorMellinPositiveCutoffFun_tsupport a b ha hab)
  exact h.toSchwartzMap (majorMellinPositiveCutoffFun_contDiff a b ha hab)

theorem majorMellinPositiveCutoff_plateau (a b : ℝ) (ha : 0 < a) (hab : a < b)
    {x : ℝ} (hx : x ∈ Icc a b) : majorMellinPositiveCutoff a b ha hab x = 1 :=
  majorMellinPositiveCutoffFun_plateau a b ha hab hx

theorem majorMellinPositiveCutoff_tsupport (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    tsupport (majorMellinPositiveCutoff a b ha hab) ⊆ Icc (a/2) (b+a/2) :=
  majorMellinPositiveCutoffFun_tsupport a b ha hab

theorem majorMellinPositiveCutoff_norm_le_one (a b : ℝ) (ha : 0 < a) (hab : a < b) (x : ℝ) :
    ‖majorMellinPositiveCutoff a b ha hab x‖ ≤ 1 := by
  change ‖(majorMellinPositiveBump a b ha hab x : ℂ)‖ ≤ 1
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (majorMellinPositiveBump a b ha hab).nonneg]
  exact (majorMellinPositiveBump a b ha hab).le_one

end
end ArtinMatthews
