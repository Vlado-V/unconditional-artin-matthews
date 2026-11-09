module

public import ArtinMatthews.SourceKPCompactChartMassBound
public import ArtinMatthews.L2FiniteChartCover


set_option backward.privateInPublic true
@[expose] public section

/-! Localize the actual quotient mass on any compact set in a fixed positive coordinate fibre. -/
namespace ArtinMatthews
open NumberField MeasureTheory SourceHyperbolicGreen Filter Set
open scoped NumberField MatrixGroups AdeleRing Topology ENNReal BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (b : SourceKPFiniteLevelFiber K hζ)

local notation "X" => ProductSpace (InfinitePlace K)
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "μ" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
local notation "ν" => productVolume (InfinitePlace K)
local notation "U" => sourceKPFiniteChartCoordinateDomain K hζ b
local notation "q" => sourceKPCompactCoordinateProjection K hζ b

theorem sourceKPCompactCoordinateFiniteCover (S : Set X) (hS : IsCompact S)
    (hSu : S ⊆ productUpper (InfinitePlace K)) :
    ∃ t : Finset (SourceKPArchUpperHalfSpace K), S ⊆ ⋃ i : t, U i.val := by
  have hcover : S ⊆ ⋃ p : SourceKPArchUpperHalfSpace K, U p := by
    intro x hx
    let p := sourceKPArchEuclideanUpperMap K x
    have he : sourceKPArchUpperEuclideanMap K p = x :=
      sourceKPArchUpperEuclideanMap_right_inverse K x (fun v => productUpper_pos (hSu hx) v)
    exact mem_iUnion.mpr ⟨p, he ▸ sourceKPFiniteChartCoordinateDomain_mem K hζ b p⟩
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover U (sourceKPFiniteChartCoordinateDomain_isOpen K hζ b) hcover
  refine ⟨t, ?_⟩
  intro x hx
  obtain ⟨p, hp⟩ := mem_iUnion.mp (ht hx)
  obtain ⟨hpt, hpu⟩ := mem_iUnion.mp hp
  exact mem_iUnion.mpr ⟨⟨p, hpt⟩, hpu⟩

theorem sourceKPCompactCoordinateProjection_ae_compact
    (S : Set X) (hS : IsCompact S) (hSu : S ⊆ productUpper (InfinitePlace K))
    {P : Y → Prop} (h : ∀ᵐ y ∂μ, P y) :
    ∀ᵐ x ∂ν, x ∈ S → P (q x) := by
  obtain ⟨t, ht⟩ := sourceKPCompactCoordinateFiniteCover K hζ b S hS hSu
  filter_upwards [ae_all_iff.mpr (fun i : t =>
    sourceKPCompactCoordinateProjection_ae_chart K hζ b i.val h)] with x hx hxS
  obtain ⟨i, hi⟩ := mem_iUnion.mp (ht hxS)
  exact hx i hi

theorem sourceKPCompactSetMassLift_exists (S : Set X) (hS : IsCompact S)
    (hSu : S ⊆ productUpper (InfinitePlace K)) :
    ∃ L : Lp ℂ 2 μ →L[ℂ] H1Mass (InfinitePlace K),
      ∀ g, (L g : X → ℂ) =ᵐ[ν] S.indicator (g ∘ q) := by
  obtain ⟨t, ht⟩ := sourceKPCompactCoordinateFiniteCover K hζ b S hS hSu
  obtain ⟨s, hs, hd, hcover, hsub⟩ := finiteChart_measurable_partition S hS.measurableSet
    (fun i : t => U i.val) (fun i => (sourceKPFiniteChartCoordinateDomain_isOpen K hζ b i.val).measurableSet) ht
  let B (i : t) := sourceKPCompactChartMassLiftCLM K hζ b i.val
  let L (i : t) := (measurableL2Cutoff ν (s i) (hs i)).comp (B i)
  refine ⟨∑ i : t, L i, ?_⟩
  intro g
  have hpiece (i : t) : (L i g : X → ℂ) =ᵐ[ν] (s i).indicator (g ∘ q) := by
    filter_upwards [measurableL2Cutoff_coe ν (s i) (hs i) (B i g),
      sourceKPCompactChartMassLiftCLM_coe K hζ b i.val g] with x hcut hchart
    change (measurableL2Cutoff ν (s i) (hs i) (B i g)) x = _
    rw [hcut]
    by_cases hx : x ∈ s i
    · simp only [Set.indicator_of_mem hx, B, hchart, Set.indicator_of_mem (hsub i hx)]
    · simp only [Set.indicator_of_notMem hx]
  have hsum : (((∑ i : t, L i) g) : X → ℂ) =ᵐ[ν] fun x => ∑ i : t, L i g x := by
    rw [ContinuousLinearMap.sum_apply]
    exact Lp.coeFn_fun_finsetSum Finset.univ (fun i => L i g)
  filter_upwards [hsum, ae_all_iff.mpr hpiece] with x hx hpieces
  rw [hx]
  by_cases hxS : x ∈ S
  · obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover ▸ hxS)
    rw [Set.indicator_of_mem hxS, Finset.sum_eq_single i]
    · rw [hpieces i, Set.indicator_of_mem hi]
    · intro j _ hji
      rw [hpieces j, Set.indicator_of_notMem]
      exact fun hj => Set.disjoint_left.mp (hd hji) hj hi
    · intro hi'
      exact (hi' (Finset.mem_univ i)).elim
  · rw [Set.indicator_of_notMem hxS]
    apply Finset.sum_eq_zero
    intro i _
    rw [hpieces i, Set.indicator_of_notMem]
    exact fun hi => hxS (hcover.symm ▸ mem_iUnion.mpr ⟨i, hi⟩)

def sourceKPCompactSetMassLift (S : Set X) (hS : IsCompact S)
    (hSu : S ⊆ productUpper (InfinitePlace K)) : Lp ℂ 2 μ →L[ℂ] H1Mass (InfinitePlace K) :=
  Classical.choose (sourceKPCompactSetMassLift_exists K hζ b S hS hSu)

theorem sourceKPCompactSetMassLift_coe (S : Set X) (hS : IsCompact S)
    (hSu : S ⊆ productUpper (InfinitePlace K)) (g : Lp ℂ 2 μ) :
    (sourceKPCompactSetMassLift K hζ b S hS hSu g : X → ℂ) =ᵐ[ν] S.indicator (g ∘ q) :=
  Classical.choose_spec (sourceKPCompactSetMassLift_exists K hζ b S hS hSu) g

theorem sourceKPCompactSetMassLift_coe_of_ae (S : Set X) (hS : IsCompact S)
    (hSu : S ⊆ productUpper (InfinitePlace K)) (g : Lp ℂ 2 μ)
    {u : Y → ℂ} (hu : (g : Y → ℂ) =ᵐ[μ] u) :
    (sourceKPCompactSetMassLift K hζ b S hS hSu g : X → ℂ) =ᵐ[ν] S.indicator (u ∘ q) := by
  have hq := sourceKPCompactCoordinateProjection_ae_compact K hζ b S hS hSu
    (P := fun y => g y = u y) hu
  filter_upwards [sourceKPCompactSetMassLift_coe K hζ b S hS hSu g, hq] with x hx hrep
  rw [hx]
  by_cases hxs : x ∈ S
  · simp only [Set.indicator_of_mem hxs, Function.comp_apply, hrep hxs]
  · simp only [Set.indicator_of_notMem hxs]

end
end ArtinMatthews
