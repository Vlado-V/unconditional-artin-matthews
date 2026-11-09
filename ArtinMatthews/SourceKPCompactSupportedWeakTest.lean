module

public import ArtinMatthews.SourceKPCompactWeakTestGlue


set_option backward.privateInPublic true
@[expose] public section

/-! Weak tests supported inside an actual region where the chart equation holds. -/
namespace ArtinMatthews
open NumberField MeasureTheory Filter SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing Topology ContDiff BigOperators Classical InnerProductSpace
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "Ω" => productUpper (InfinitePlace K)
local notation "μ" => productVolume (InfinitePlace K)
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
local notation "T" => sourceKPCompactC2Core K hζ

theorem sourceKPCompactCore_weak_of_chart_supported (φ w χ : T) (F : Y → ℂ)
    (hF : Continuous F) (U : Set Y) (hχ : ∀ y ∈ tsupport φ.val, χ.val y = 1)
    (hχU : tsupport χ.val ⊆ U)
    (hweak : ∀ (b : SourceKPFiniteLevelFiber K hζ) (ψ : h1Tests (InfinitePlace K) 2),
      (∀ x ∈ tsupport ψ.val, x ∈ Ω ∧
        sourceKPUpperToCompact K hζ b (sourceKPArchEuclideanUpperMap K x) ∈ U) →
      (∫ x, productGradientPair ψ.val (sourceKPCompactChartPullback K hζ w.val b) x ∂μ) =
        ∫ x, star (ψ.val x)*sourceKPCompactChartPullback K hζ F b x ∂μ) :
    sourceKPCompactDirichletCore K hζ φ w = ∫ y, star (φ.val y)*F y ∂μY := by
  obtain ⟨I,b,p,η,hη⟩ := sourceKPCompactCore_sum_periodized_tests K hζ φ
  let ξ i := sourceKPCompactCoreLocalized K hζ χ (b i) (p i) (η i)
  let ψ (i : Y) : T := sourceKPChartPeriodizationCore K hζ (b i) (ξ i).val
  have hp (i : Y) : (ψ i).val =
      sourceKPChartPeriodizationGlobal K hζ (b i) (η i).val*χ.val :=
    sourceKPChartPeriodizationGlobal_localized K hζ χ (b i) (p i) (η i)
  have hsum (y : Y) : φ.val y = ∑ i ∈ I, (ψ i).val y := by
    simp_rw [hp,Pi.mul_apply,← Finset.sum_mul,← congrFun hη y]
    by_cases hy : y ∈ tsupport φ.val
    · rw [hχ y hy,mul_one]
    · rw [image_eq_zero_of_notMem_tsupport hy,zero_mul]
  have hψ : φ = ∑ i ∈ I, ψ i := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    funext y
    simpa only [Finset.sum_apply] using hsum y
  have htest (i : Y) :
      sourceKPCompactDirichletCore K hζ (ψ i) w = ∫ y, star ((ψ i).val y)*F y ∂μY := by
    apply sourceKPPeriodizedWeakTest K hζ (b i) (p i) (ξ i) w.val F hF.measurable w
      (fun _ _ => EventuallyEq.rfl)
    intro ζ hζsupp
    apply hweak (b i) ζ
    intro x hx
    refine ⟨(hζsupp x hx).1,hχU ?_⟩
    have h := (hζsupp x hx).2
    change _ ∈ tsupport (ψ i).val at h
    rw [hp i] at h
    exact tsupport_mul_subset_right h
  calc
    _ = ∑ i ∈ I, sourceKPCompactDirichletCore K hζ (ψ i) w := by
      rw [hψ]
      unfold sourceKPCompactDirichletCore
      rw [← integral_finsetSum _ (fun i _ => sourceKPCompactCorePairDensity_integrable K hζ (ψ i) w)]
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by
        simp only [sourceKPCompactCorePairDensity,map_sum,sum_inner]
    _ = ∑ i ∈ I, ∫ y, star ((ψ i).val y)*F y ∂μY :=
      Finset.sum_congr rfl (fun i _ => htest i)
    _ = _ := by
      rw [← integral_finsetSum _ (fun i _ => sourceKPCompactCore_test_pair_integrable K hζ (ψ i) F hF)]
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by
        change (∑ i ∈ I, star ((ψ i).val y)*F y) = star (φ.val y)*F y
        rw [hsum y,star_sum,Finset.sum_mul]

end
end ArtinMatthews
