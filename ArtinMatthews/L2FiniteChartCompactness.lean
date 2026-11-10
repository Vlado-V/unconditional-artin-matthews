module

public import ArtinMatthews.L2MeasurableCutoff
public import ArtinMatthews.L2ChartRestriction


set_option backward.privateInPublic true
@[expose] public section

/-! Finite measurable partitions transfer local L2 compactness with explicit chart constants. -/
namespace ArtinMatthews
open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators
noncomputable section

theorem totallyBounded_range_of_dist_le {κ M N : Type*}
    [PseudoMetricSpace M] [PseudoMetricSpace N]
    (f : κ → M) (g : κ → N) (C : ℝ) (hC : 0 ≤ C)
    (hf : TotallyBounded (range f))
    (hfg : ∀ a b, dist (g a) (g b) ≤ C * dist (f a) (f b)) :
    TotallyBounded (range g) := by
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  have hCp : 0 < C + 1 := by linarith
  obtain ⟨t, htrange, ht, hcover⟩ :=
    Metric.finite_approx_of_totallyBounded hf (ε / (C + 1)) (div_pos hε hCp)
  have hpre : ∀ y : t, ∃ a, f a = (y : M) := fun y => htrange y.property
  choose a ha using hpre
  let : Finite t := ht
  refine ⟨range (fun y : t => g (a y)), Set.finite_range _, ?_⟩
  rintro _ ⟨k, rfl⟩
  have hnear := hcover (mem_range_self k)
  simp only [mem_iUnion, Metric.mem_ball] at hnear ⊢
  obtain ⟨y, hyt, hdy⟩ := hnear
  refine ⟨g (a ⟨y, hyt⟩), mem_range_self _, ?_⟩
  have hdist := hfg k (a ⟨y, hyt⟩)
  rw [ha] at hdist
  have hnonneg : 0 ≤ dist (f k) y := dist_nonneg
  have hlt : (C + 1) * dist (f k) y < ε := by
    simpa only [mul_comm] using (lt_div_iff₀ hCp).mp hdy
  nlinarith

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
variable {J : Type*} [Fintype J]

theorem measurableL2Cutoff_finite_partition (S : Set X) (hS : MeasurableSet S)
    (s : J → Set X) (hs : ∀ j, MeasurableSet (s j))
    (hdisjoint : Pairwise fun i j => Disjoint (s i) (s j))
    (hcover : S = ⋃ j, s j) (f : HeightL2 μ) :
    measurableL2Cutoff μ S hS f = ∑ j, measurableL2Cutoff μ (s j) (hs j) f := by
  apply Lp.ext
  filter_upwards [measurableL2Cutoff_coe μ S hS f,
    ae_all_iff.mpr (fun j => measurableL2Cutoff_coe μ (s j) (hs j) f),
    Lp.coeFn_fun_finsetSum Finset.univ (fun j => measurableL2Cutoff μ (s j) (hs j) f)]
    with x hglobal hpieces hsum
  rw [hglobal, hsum]
  by_cases hx : x ∈ S
  · have hxu : x ∈ ⋃ j, s j := hcover ▸ hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hxu
    rw [indicator_of_mem hx, Finset.sum_eq_single i]
    · rw [hpieces i, indicator_of_mem hxi]
    · intro j _ hji
      rw [hpieces j, indicator_of_notMem]
      exact fun hxj => Set.disjoint_left.mp (hdisjoint hji) hxj hxi
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  · rw [indicator_of_notMem hx]
    symm
    apply Finset.sum_eq_zero
    intro j _
    rw [hpieces j, indicator_of_notMem]
    exact fun hxj => hx (hcover.symm ▸ mem_iUnion.mpr ⟨j, hxj⟩)

variable (Y : J → Type*) [∀ j, MeasurableSpace (Y j)]
variable (ν ρ : ∀ j, Measure (Y j))

theorem finiteChart_l2_dist_le_sum
    (S : Set X) (hS : MeasurableSet S)
    (s : J → Set X) (hs : ∀ j, MeasurableSet (s j))
    (hdisjoint : Pairwise fun i j => Disjoint (s i) (s j))
    (hcover : S = ⋃ j, s j)
    (q : ∀ j, Y j → X) (hq : ∀ j, Measurable (q j))
    (C : J → ℝ) (hC : ∀ j, 0 ≤ C j) (hρν : ∀ j, ρ j ≤ ν j)
    (hμ : ∀ j, μ.restrict (s j) ≤ ENNReal.ofReal (C j) • Measure.map (q j) (ρ j))
    (f g : HeightL2 μ) (F G : ∀ j, HeightL2 (ν j))
    (hf : ∀ j, ∀ᵐ y ∂ρ j, q j y ∈ s j → f (q j y) = F j y)
    (hg : ∀ j, ∀ᵐ y ∂ρ j, q j y ∈ s j → g (q j y) = G j y) :
    dist (measurableL2Cutoff μ S hS f) (measurableL2Cutoff μ S hS g) ≤
      ∑ j, Real.sqrt (C j) * dist (F j) (G j) := by
  rw [dist_eq_norm, ← map_sub,
    measurableL2Cutoff_finite_partition μ S hS s hs hdisjoint hcover]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  simpa only [map_sub, dist_eq_norm] using
    l2_chart_cutoff_dist_le μ (ν j) (ρ j) (hρν j) (s j) (hs j) (q j) (hq j)
      (C j) (hC j) (hμ j) f g (F j) (G j) (hf j) (hg j)

theorem finiteChart_l2_dist_le_pi
    (S : Set X) (hS : MeasurableSet S)
    (s : J → Set X) (hs : ∀ j, MeasurableSet (s j))
    (hdisjoint : Pairwise fun i j => Disjoint (s i) (s j))
    (hcover : S = ⋃ j, s j)
    (q : ∀ j, Y j → X) (hq : ∀ j, Measurable (q j))
    (C : J → ℝ) (hC : ∀ j, 0 ≤ C j) (hρν : ∀ j, ρ j ≤ ν j)
    (hμ : ∀ j, μ.restrict (s j) ≤ ENNReal.ofReal (C j) • Measure.map (q j) (ρ j))
    (f g : HeightL2 μ) (F G : ∀ j, HeightL2 (ν j))
    (hf : ∀ j, ∀ᵐ y ∂ρ j, q j y ∈ s j → f (q j y) = F j y)
    (hg : ∀ j, ∀ᵐ y ∂ρ j, q j y ∈ s j → g (q j y) = G j y) :
    dist (measurableL2Cutoff μ S hS f) (measurableL2Cutoff μ S hS g) ≤
      (∑ j, Real.sqrt (C j)) * dist F G := by
  apply (finiteChart_l2_dist_le_sum μ Y ν ρ S hS s hs hdisjoint hcover q hq C hC hρν hμ
    f g F G hf hg).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  simpa only [dist_eq_norm, Pi.sub_apply] using norm_le_pi_norm (F - G) j

theorem finiteChart_l2_isCompact_closure {κ : Type*}
    (S : Set X) (hS : MeasurableSet S)
    (s : J → Set X) (hs : ∀ j, MeasurableSet (s j))
    (hdisjoint : Pairwise fun i j => Disjoint (s i) (s j))
    (hcover : S = ⋃ j, s j)
    (q : ∀ j, Y j → X) (hq : ∀ j, Measurable (q j))
    (C : J → ℝ) (hC : ∀ j, 0 ≤ C j) (hρν : ∀ j, ρ j ≤ ν j)
    (hμ : ∀ j, μ.restrict (s j) ≤ ENNReal.ofReal (C j) • Measure.map (q j) (ρ j))
    (f : κ → HeightL2 μ) (F : ∀ j, κ → HeightL2 (ν j))
    (hf : ∀ j k, ∀ᵐ y ∂ρ j, q j y ∈ s j → f k (q j y) = F j k y)
    (hlocal : ∀ j, IsCompact (closure (range (F j)))) :
    IsCompact (closure (range (fun k => measurableL2Cutoff μ S hS (f k)))) := by
  have hproduct := isCompact_pi_infinite hlocal
  have htotal : TotallyBounded (range (fun k j => F j k)) := by
    apply hproduct.totallyBounded.subset
    rintro _ ⟨k, rfl⟩ j
    exact subset_closure (mem_range_self k)
  have hresult := totallyBounded_range_of_dist_le (fun k j => F j k)
    (fun k => measurableL2Cutoff μ S hS (f k)) (∑ j, Real.sqrt (C j))
    (Finset.sum_nonneg fun j _ => Real.sqrt_nonneg _) htotal
    (fun a b => finiteChart_l2_dist_le_pi μ Y ν ρ S hS s hs hdisjoint hcover q hq C hC hρν hμ
      (f a) (f b) (fun j => F j a) (fun j => F j b) (fun j => hf j a) (fun j => hf j b))
  exact hresult.closure.isCompact_of_isClosed isClosed_closure

end
end ArtinMatthews
