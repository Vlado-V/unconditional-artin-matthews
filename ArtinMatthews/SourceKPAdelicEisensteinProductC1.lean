module

public import ArtinMatthews.SourceKPAdelicProductDerivative
public import ArtinMatthews.SourceKPAdelicProductCompactBound
public import ArtinMatthews.SourceHyperbolicProductMeasure
public import Mathlib.Analysis.Calculus.SmoothSeries


set_option backward.privateInPublic true
@[expose] public section

/-! The actual Eisenstein series is continuously differentiable in
all archimedean coordinates throughout its proved convergence region. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix OAI.CubicEisenstein SourceArchJacquet
open SourceHyperbolicGreen Filter Metric
open scoped NumberField MatrixGroups AdeleRing ContDiff Topology BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicRationalProductChart_compact_fderiv_bound {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (q : SourceKPAdelicProjective K hζ) (S : Set (InfinitePlace K → EuclideanSpatial))
    (hS : IsCompact S) (hpos : ∀ p ∈ S, ∀ v, 0 < p v 2) :
    ∃ M : SourceKPRationalBorelCoset K → ℝ, Summable M ∧
      ∀ c p, p ∈ S → ‖fderiv ℝ (sourceKPAdelicRationalProductChart K hζ s q c) p‖ ≤ M c := by
  obtain ⟨M,hM,hbound⟩ := sourceKPAdelicRationalProductChart_compact_bound K hζ hs q S hS hpos
  let L : (InfinitePlace K → EuclideanSpatial) → ℝ := fun p => ∑ v, 3*‖2*s+1‖/(p v 2)
  have hL : ContinuousOn L S := by
    apply continuousOn_finsetSum
    intro v _
    have hv : Continuous (fun p : InfinitePlace K → EuclideanSpatial => p v 2) :=
      (EuclideanSpace.proj 2).continuous.comp (continuous_apply v)
    exact continuousOn_const.div hv.continuousOn (fun p hp => (hpos p hp v).ne')
  obtain ⟨B,hB⟩ := hS.bddAbove_image hL
  refine ⟨fun c => max B 0*M c,hM.mul_left _,?_⟩
  intro c p hp
  have hLp : L p ≤ max B 0 := (hB ⟨p,hp,rfl⟩).trans (le_max_left _ _)
  calc
    ‖fderiv ℝ (sourceKPAdelicRationalProductChart K hζ s q c) p‖ ≤
        L p*‖sourceKPAdelicRationalProductChart K hζ s q c p‖ :=
      sourceKPAdelicRationalProductChart_fderiv_bound K hζ s q c p (hpos p hp)
    _ ≤ max B 0*‖sourceKPAdelicRationalProductChart K hζ s q c p‖ :=
      mul_le_mul_of_nonneg_right hLp (norm_nonneg _)
    _ ≤ max B 0*M c := mul_le_mul_of_nonneg_left (hbound c p hp) (le_max_right _ _)

theorem sourceKPAdelicEisensteinProductChart_contDiffAt {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (q : SourceKPAdelicProjective K hζ) (p : InfinitePlace K → EuclideanSpatial)
    (hp : ∀ v, 0 < p v 2) :
    ContDiffAt ℝ 1 (sourceKPAdelicEisensteinProductChart K hζ s q) p := by
  have hpU : p ∈ productUpper (InfinitePlace K) := fun v _ => hp v
  obtain ⟨r,hr,hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((productUpper_isOpen (InfinitePlace K)).mem_nhds hpU)
  have hpos (x : InfinitePlace K → EuclideanSpatial) (hx : x ∈ closedBall p r) :
      ∀ v, 0 < x v 2 := fun v => hsub hx v (Set.mem_univ v)
  obtain ⟨M,hM,hbound⟩ := sourceKPAdelicRationalProductChart_compact_fderiv_bound
    K hζ hs q (closedBall p r) (isCompact_closedBall p r) hpos
  let F := sourceKPAdelicRationalProductChart K hζ s q
  let D := fun c x => fderiv ℝ (F c) x
  have hFderiv (c : SourceKPRationalBorelCoset K) (x : InfinitePlace K → EuclideanSpatial)
      (hx : x ∈ ball p r) : HasFDerivAt (F c) (D c x) x :=
    ((sourceKPAdelicRationalProductChart_contDiffAt K hζ s q c x
      (hpos x (ball_subset_closedBall hx))).differentiableAt (by simp)).hasFDerivAt
  have hDbound (c : SourceKPRationalBorelCoset K) (x : InfinitePlace K → EuclideanSpatial)
      (hx : x ∈ ball p r) : ‖D c x‖ ≤ M c := hbound c x (ball_subset_closedBall hx)
  have hDcont (c : SourceKPRationalBorelCoset K) : ContinuousOn (D c) (ball p r) := by
    have hc : ContDiffOn ℝ 1 (F c) (ball p r) := by
      intro x hx
      exact ((sourceKPAdelicRationalProductChart_contDiffAt K hζ s q c x
        (hpos x (ball_subset_closedBall hx))).of_le (by simp)).contDiffWithinAt
    exact hc.continuousOn_fderiv_of_isOpen isOpen_ball (by norm_num)
  have hsum0 : Summable (fun c => F c p) := by
    have h := sourceKPAdelicCompactEisenstein_converges K hζ hs
      (q*(ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ p hp),1))
    change Summable (fun c : SourceKPRationalBorelCoset K =>
      sourceKPAdelicRationalSummand K hζ
        (sourceKPAdelicPrincipalSeriesScalar K hζ s (sourceKPAdelicCompactSection K hζ s))
        (q*(ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ p hp),1)) c) at h
    simpa only [F,sourceKPAdelicRationalProductChart,dite_eq_left hp] using h
  have hsumDeriv (x : InfinitePlace K → EuclideanSpatial) (hx : x ∈ ball p r) :
      HasFDerivAt (fun y => ∑' c, F c y) (∑' c, D c x) x :=
    hasFDerivAt_tsum_of_isPreconnected hM isOpen_ball (convex_ball p r).isPreconnected
      hFderiv hDbound (mem_ball_self hr) hsum0 hx
  have hDsum : ContinuousOn (fun x => ∑' c, D c x) (ball p r) :=
    continuousOn_tsum hDcont hM hDbound
  have he : sourceKPAdelicEisensteinProductChart K hζ s q = fun y => ∑' c, F c y := by
    funext y
    exact sourceKPAdelicEisensteinProductChart_tsum K hζ s q y
  rw [he]
  change ContDiffAt ℝ ((0 : ℕ)+1) (fun y => ∑' c, F c y) p
  rw [contDiffAt_succ_iff_hasFDerivAt]
  refine ⟨fun x => ∑' c, D c x,⟨ball p r,ball_mem_nhds p hr,hsumDeriv⟩,?_⟩
  change ContDiffAt ℝ 0 (fun x => ∑' c, D c x) p
  exact contDiffAt_zero.mpr ⟨ball p r,ball_mem_nhds p hr,hDsum⟩

theorem sourceKPAdelicEisensteinProductChart_contDiffOn {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (q : SourceKPAdelicProjective K hζ) :
    ContDiffOn ℝ 1 (sourceKPAdelicEisensteinProductChart K hζ s q)
      (productUpper (InfinitePlace K)) := by
  intro p hp
  exact (sourceKPAdelicEisensteinProductChart_contDiffAt K hζ hs q p
    (fun v => hp v (Set.mem_univ v))).contDiffWithinAt

end
end ArtinMatthews
