module

public import ArtinMatthews.FullMainActualCubicInput
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension


set_option backward.privateInPublic true
@[expose] public section

/-! A fixed cutoff and a fixed positive giant-prime exponent for the
original final theorem. -/

noncomputable section
namespace ArtinMatthews

open Set
open scoped ContDiff

def giantMainEpsilon : ℝ := 1/2000000

theorem giantMainEpsilon_bounds : 0 < giantMainEpsilon ∧ giantMainEpsilon < 1/1000000 := by
  norm_num [giantMainEpsilon]

private def giantMainCutoffBump : ContDiffBump (3/2 : ℝ) where
  rIn := 1/8
  rOut := 1/4
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def giantMainSmoothCutoff : ℝ → ℝ := giantMainCutoffBump

theorem giantMainSmoothCutoff_spec :
    ContDiff ℝ ∞ giantMainSmoothCutoff ∧
      HasCompactSupport giantMainSmoothCutoff ∧
      tsupport giantMainSmoothCutoff ⊆ Ioo (1 : ℝ) 2 ∧
      (∀ t, 0 ≤ giantMainSmoothCutoff t ∧ giantMainSmoothCutoff t ≤ 1) ∧
      ∃ t, giantMainSmoothCutoff t ≠ 0 := by
  have hs : tsupport giantMainSmoothCutoff ⊆ Ioo (1 : ℝ) 2 := by
    change tsupport (giantMainCutoffBump : ℝ → ℝ) ⊆ Ioo (1 : ℝ) 2
    rw [giantMainCutoffBump.tsupport_eq]
    intro t ht
    rw [Metric.mem_closedBall,Real.dist_eq,abs_le] at ht
    change -(1/4 : ℝ) ≤ t-3/2 ∧ t-3/2 ≤ 1/4 at ht
    exact ⟨by linarith only [ht.1],by linarith only [ht.2]⟩
  have hc : giantMainSmoothCutoff (3/2)=1 := giantMainCutoffBump.one_of_mem_closedBall
    (Metric.mem_closedBall_self giantMainCutoffBump.rIn_pos.le)
  refine ⟨giantMainCutoffBump.contDiff,giantMainCutoffBump.hasCompactSupport,hs,
    fun t => ⟨giantMainCutoffBump.nonneg,giantMainCutoffBump.le_one⟩,3/2,?_⟩
  rw [hc]
  exact one_ne_zero

theorem fullMainStatement_of_fixed_tuple_angular_inputs
    (htuple : GiantOrdinaryTupleCancellationInput giantMainEpsilon giantMainSmoothCutoff)
    (hsource : GiantAngularSourceInput) : FullMainStatement := by
  obtain ⟨hε,hεδ⟩ := giantMainEpsilon_bounds
  obtain ⟨hsmooth,hcompact,hsupp,hrange,hnonzero⟩ := giantMainSmoothCutoff_spec
  exact fullMainStatement_of_actual_tuple_angular_inputs hε hεδ giantMainSmoothCutoff
    hsmooth hcompact hsupp hrange hnonzero htuple hsource

end ArtinMatthews
