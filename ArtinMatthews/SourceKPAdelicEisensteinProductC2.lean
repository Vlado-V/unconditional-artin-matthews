module

public import ArtinMatthews.SourceKPAdelicProductSecondDerivative


set_option backward.privateInPublic true
@[expose] public section

/-! Twice-continuous differentiability of the actual initial rational sum. -/

namespace ArtinMatthews
open NumberField Matrix OAI.CubicEisenstein SourceArchJacquet SourceHyperbolicGreen Filter Metric
open scoped NumberField MatrixGroups AdeleRing ContDiff Topology BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicEisensteinProductChart_contDiffAt_two {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (q : SourceKPAdelicProjective K hζ) (p : InfinitePlace K → EuclideanSpatial)
    (hp : ∀ v, 0 < p v 2) :
    ContDiffAt ℝ 2 (sourceKPAdelicEisensteinProductChart K hζ s q) p := by
  have hpU : p ∈ productUpper (InfinitePlace K) := fun v _ => hp v
  obtain ⟨r,hr,hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((productUpper_isOpen (InfinitePlace K)).mem_nhds hpU)
  let S := closedBall p r
  have hS : IsCompact S := isCompact_closedBall _ _
  have hpos (x : InfinitePlace K → EuclideanSpatial) (hx : x ∈ S) :
      ∀ v, 0 < x v 2 := fun v => hsub hx v (Set.mem_univ v)
  obtain ⟨M₀,hM₀,hb₀⟩ := sourceKPAdelicRationalProductChart_compact_bound K hζ hs q S hS hpos
  obtain ⟨M₁,hM₁,hb₁⟩ :=
    sourceKPAdelicRationalProductChart_compact_fderiv_bound K hζ hs q S hS hpos
  obtain ⟨M₂,hM₂,hb₂⟩ :=
    sourceKPAdelicRationalProductChart_compact_second_bound K hζ hs q S hS hpos
  let F := sourceKPAdelicRationalProductChart K hζ s q
  let D₁ := fun c => fderiv ℝ (F c)
  let D₂ := fun c => fderiv ℝ (D₁ c)
  have hF (c : SourceKPRationalBorelCoset K) (x : InfinitePlace K → EuclideanSpatial)
      (hx : x ∈ ball p r) : ContDiffAt ℝ (∞ : ℕ∞ω) (F c) x :=
    sourceKPAdelicRationalProductChart_contDiffAt K hζ s q c x (hpos x (ball_subset_closedBall hx))
  have hD₁ (c : SourceKPRationalBorelCoset K) (x : InfinitePlace K → EuclideanSpatial)
      (hx : x ∈ ball p r) : ContDiffAt ℝ 1 (D₁ c) x :=
    (hF c x hx).fderiv_right (m := 1) (by simp)
  have hD₂ (c : SourceKPRationalBorelCoset K) : ContinuousOn (D₂ c) (ball p r) :=
    fun x hx => ((hD₁ c x hx).fderiv_right (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  have hB₂ (c : SourceKPRationalBorelCoset K) (x : InfinitePlace K → EuclideanSpatial)
      (hx : x ∈ ball p r) : ‖D₂ c x‖ ≤ M₂ c := hb₂ c x (ball_subset_closedBall hx)
  have hD₂sum : ContinuousOn (fun x => ∑' c, D₂ c x) (ball p r) :=
    continuousOn_tsum (f := D₂) hD₂ hM₂ hB₂
  have h₀sum : Summable (fun c => F c p) :=
    .of_norm_bounded hM₀ (fun c => hb₀ c p (mem_closedBall_self hr.le))
  have h₁sum : Summable (fun c => D₁ c p) :=
    .of_norm_bounded hM₁ (fun c => hb₁ c p (mem_closedBall_self hr.le))
  have hFsum (x : InfinitePlace K → EuclideanSpatial) (hx : x ∈ ball p r) :
      HasFDerivAt (fun y => ∑' c, F c y) (∑' c, D₁ c x) x :=
    hasFDerivAt_tsum_of_isPreconnected hM₁ isOpen_ball (convex_ball p r).isPreconnected
      (fun c y hy => ((hF c y hy).differentiableAt (by simp)).hasFDerivAt)
      (fun c y hy => hb₁ c y (ball_subset_closedBall hy)) (mem_ball_self hr) h₀sum hx
  have hD₁sum (x : InfinitePlace K → EuclideanSpatial) (hx : x ∈ ball p r) :
      HasFDerivAt (fun y => ∑' c, D₁ c y) (∑' c, D₂ c x) x :=
    hasFDerivAt_tsum_of_isPreconnected hM₂ isOpen_ball (convex_ball p r).isPreconnected
      (fun c y hy => ((hD₁ c y hy).differentiableAt (by norm_num)).hasFDerivAt)
      (fun c y hy => hb₂ c y (ball_subset_closedBall hy)) (mem_ball_self hr) h₁sum hx
  have hC₁ : ContDiffAt ℝ 1 (fun y => ∑' c, D₁ c y) p := by
    change ContDiffAt ℝ ((0 : ℕ)+1) (fun y => ∑' c, D₁ c y) p
    rw [contDiffAt_succ_iff_hasFDerivAt]
    refine ⟨fun x => ∑' c, D₂ c x,⟨ball p r,ball_mem_nhds p hr,hD₁sum⟩,?_⟩
    change ContDiffAt ℝ 0 (fun x => ∑' c, D₂ c x) p
    exact contDiffAt_zero.mpr ⟨ball p r,ball_mem_nhds p hr,hD₂sum⟩
  have he : sourceKPAdelicEisensteinProductChart K hζ s q = fun y => ∑' c, F c y :=
    funext (sourceKPAdelicEisensteinProductChart_tsum K hζ s q)
  rw [he]
  change ContDiffAt ℝ ((1 : ℕ)+1) (fun y => ∑' c, F c y) p
  rw [contDiffAt_succ_iff_hasFDerivAt]
  exact ⟨fun x => ∑' c, D₁ c x,⟨ball p r,ball_mem_nhds p hr,hFsum⟩,hC₁⟩

theorem sourceKPAdelicEisensteinProductChart_contDiffOn_two {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (q : SourceKPAdelicProjective K hζ) :
    ContDiffOn ℝ 2 (sourceKPAdelicEisensteinProductChart K hζ s q)
      (productUpper (InfinitePlace K)) :=
  fun p hp => (sourceKPAdelicEisensteinProductChart_contDiffAt_two K hζ hs q p
    (fun v => hp v (Set.mem_univ v))).contDiffWithinAt

end
end ArtinMatthews
