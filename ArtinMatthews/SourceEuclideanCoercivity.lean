module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.MetricSpace.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine quadratic form stays coercive near a point where its
coefficient is continuous and positive definite. -/

namespace ArtinMatthews

open Set Filter
open scoped Topology

theorem sourceElliptic_coercive_near_point {E V : Type*} [TopologicalSpace E]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] {U : Set E}
    (hU : IsOpen U) {x : E} (hx : x ∈ U) (A : E → V →L[ℝ] V)
    (hA : ContinuousOn A U) {a : ℝ} (ha : 0 < a)
    (hpos : ∀ w : V, a*‖w‖*‖w‖ ≤ inner ℝ (A x w) w) :
    ∃ W : Set E, IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧
      ∀ y ∈ W, ∀ w : V, (a/2)*‖w‖*‖w‖ ≤ inner ℝ (A y w) w := by
  have hClose : {y | A y ∈ Metric.ball (A x) (a/2)} ∈ 𝓝 x :=
    (hA.continuousAt (hU.mem_nhds hx)).preimage_mem_nhds (Metric.ball_mem_nhds _ (half_pos ha))
  obtain ⟨W,hW,hWo,hxW⟩ := mem_nhds_iff.mp (inter_mem (hU.mem_nhds hx) hClose)
  refine ⟨W,hWo,hxW,fun _ hy => (hW hy).1,?_⟩
  intro y hy w
  have hdist : ‖A x-A y‖ ≤ a/2 := by
    rw [norm_sub_rev,← dist_eq_norm]
    exact (show dist (A y) (A x) < a/2 from (hW hy).2).le
  have hbound : inner ℝ ((A x-A y) w) w ≤ (a/2)*‖w‖*‖w‖ :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
      (((A x-A y).le_opNorm w).trans (mul_le_mul_of_nonneg_right hdist (norm_nonneg _))) (norm_nonneg _))
  rw [ContinuousLinearMap.sub_apply,inner_sub_left] at hbound
  calc
    _ = a*‖w‖*‖w‖ - (a/2)*‖w‖*‖w‖ := by ring
    _ ≤ inner ℝ (A x w) w - (inner ℝ (A x w) w - inner ℝ (A y w) w) :=
      sub_le_sub (hpos w) hbound
    _ = _ := sub_sub_cancel _ _

end ArtinMatthews
