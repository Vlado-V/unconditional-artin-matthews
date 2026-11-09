module

public import ArtinMatthews.SourceKPCompactEnergyRegularity


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine locally finite periodization of compact tests by the arithmetic chart subgroup. -/
namespace ArtinMatthews
open NumberField Matrix MeasureTheory Filter SourceHyperbolicGreen SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing Topology ContDiff BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPChartTestUpperSupport (φ : h1Tests (InfinitePlace K) 2) : Set (SourceKPArchUpperHalfSpace K) :=
  sourceKPArchEuclideanUpperMap K '' tsupport φ.val

theorem sourceKPChartTestUpperSupport_compact (φ : h1Tests (InfinitePlace K) 2) :
    IsCompact (sourceKPChartTestUpperSupport K φ) :=
  φ.prop.2.1.image_of_continuousOn ((sourceKPArchEuclideanUpperMap_continuousOn K).mono φ.prop.2.2)

theorem sourceKPChartTest_mem_upperSupport (φ : h1Tests (InfinitePlace K) 2)
    (p : SourceKPArchUpperHalfSpace K) (hp : φ.val (sourceKPArchUpperEuclideanMap K p) ≠ 0) :
    p ∈ sourceKPChartTestUpperSupport K φ :=
  ⟨sourceKPArchUpperEuclideanMap K p,subset_tsupport φ.val hp,
    sourceKPArchUpperEuclideanMap_left_inverse K p⟩

def sourceKPChartPeriodTerm (b : SourceKPFiniteLevelFiber K hζ) (φ : h1Tests (InfinitePlace K) 2)
    (γ : sourceKPArchComponentSubgroup K hζ b) (p : SourceKPArchUpperHalfSpace K) : ℂ :=
  φ.val (sourceKPArchUpperEuclideanMap K (γ⁻¹ • p))

def sourceKPChartPeriodization (b : SourceKPFiniteLevelFiber K hζ) (φ : h1Tests (InfinitePlace K) 2)
    (p : SourceKPArchUpperHalfSpace K) : ℂ :=
  ∑' γ : sourceKPArchComponentSubgroup K hζ b, sourceKPChartPeriodTerm K hζ b φ γ p

theorem sourceKPChartPeriodTerm_locally_finite (b : SourceKPFiniteLevelFiber K hζ)
    (φ : h1Tests (InfinitePlace K) 2) (p : SourceKPArchUpperHalfSpace K) :
    ∃ I : Finset (sourceKPArchComponentSubgroup K hζ b),
      ∀ᶠ q in 𝓝 p, ∀ γ ∉ I, sourceKPChartPeriodTerm K hζ b φ γ q = 0 := by
  let c := sourceKPUpperFiniteChart K hζ b p
  let S := sourceKPChartTestUpperSupport K φ
  have hf := ProperlyDiscontinuousSMul.finite_disjoint_inter_image
    (Γ := sourceKPArchComponentSubgroup K hζ b) (sourceKPChartTestUpperSupport_compact K φ) c.isCompact_closure
  refine ⟨hf.toFinset,?_⟩
  filter_upwards [c.isOpen_domain.mem_nhds c.center_mem] with q hq
  intro γ hγ
  by_contra hn
  have hs : γ⁻¹ • q ∈ S := sourceKPChartTest_mem_upperSupport K φ _ hn
  have hhit : ((γ • ·) '' S ∩ closure (c.domain : Set (SourceKPArchUpperHalfSpace K))).Nonempty :=
    ⟨q,⟨⟨γ⁻¹ • q,hs,smul_inv_smul γ q⟩,subset_closure hq⟩⟩
  apply hγ
  rw [Set.Finite.mem_toFinset]
  change ((γ • ·) '' S ∩ closure (c.domain : Set (SourceKPArchUpperHalfSpace K))).Nonempty
  exact hhit

theorem sourceKPChartPeriodization_continuous (b : SourceKPFiniteLevelFiber K hζ)
    (φ : h1Tests (InfinitePlace K) 2) : Continuous (sourceKPChartPeriodization K hζ b φ) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  obtain ⟨I,hI⟩ := sourceKPChartPeriodTerm_locally_finite K hζ b φ p
  have hc : Continuous (fun q => ∑ γ ∈ I, sourceKPChartPeriodTerm K hζ b φ γ q) := by
    apply continuous_finsetSum
    intro γ _
    exact φ.prop.1.continuous.comp ((sourceKPArchUpperEuclideanMap_continuous K).comp
      (continuous_const_smul γ⁻¹))
  apply hc.continuousAt.congr_of_eventuallyEq
  filter_upwards [hI] with q hq
  exact tsum_eq_sum hq

theorem sourceKPChartPeriodization_contDiffOn (b : SourceKPFiniteLevelFiber K hζ)
    (φ : h1Tests (InfinitePlace K) 2) :
    ContDiffOn ℝ 2 (sourceKPChartPeriodization K hζ b φ ∘ sourceKPArchEuclideanUpperMap K)
      (productUpper (InfinitePlace K)) := by
  intro x hx
  apply ContDiffAt.contDiffWithinAt
  obtain ⟨I,hI⟩ := sourceKPChartPeriodTerm_locally_finite K hζ b φ (sourceKPArchEuclideanUpperMap K x)
  have hA := (sourceKPArchEuclideanUpperMap_continuousOn K x hx).continuousAt
    ((productUpper_isOpen (InfinitePlace K)).mem_nhds hx)
  have hc : ContDiffAt ℝ 2 (fun y => ∑ γ ∈ I,
      φ.val (sourceKPArchEuclideanAction K hζ γ⁻¹.val y)) x := by
    apply ContDiffAt.sum
    intro γ _
    exact φ.prop.1.contDiffAt.comp x
      ((sourceKPArchEuclideanAction_contDiffAt K hζ γ⁻¹.val x hx).of_le (by simp))
  apply hc.congr_of_eventuallyEq
  filter_upwards [hA.tendsto.eventually hI] with q hq
  change sourceKPChartPeriodization K hζ b φ (sourceKPArchEuclideanUpperMap K q) = _
  rw [sourceKPChartPeriodization,tsum_eq_sum hq]
  rfl

theorem sourceKPChartPeriodization_smul (b : SourceKPFiniteLevelFiber K hζ)
    (φ : h1Tests (InfinitePlace K) 2) (δ : sourceKPArchComponentSubgroup K hζ b)
    (p : SourceKPArchUpperHalfSpace K) :
    sourceKPChartPeriodization K hζ b φ (δ • p) = sourceKPChartPeriodization K hζ b φ p := by
  unfold sourceKPChartPeriodization
  calc
    _ = ∑' γ : sourceKPArchComponentSubgroup K hζ b,
        sourceKPChartPeriodTerm K hζ b φ ((Equiv.mulLeft δ⁻¹) γ) p := by
      apply tsum_congr
      intro γ
      simp only [sourceKPChartPeriodTerm,Equiv.coe_mulLeft,_root_.mul_inv_rev,inv_inv,mul_smul]
    _ = _ := (Equiv.mulLeft δ⁻¹).tsum_eq (fun γ => sourceKPChartPeriodTerm K hζ b φ γ p)

end
end ArtinMatthews
