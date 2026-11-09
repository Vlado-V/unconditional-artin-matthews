module

public import ArtinMatthews.SourceKPPeriodizedWeakTest
public import ArtinMatthews.SourceKPCompactTestPartition
public import ArtinMatthews.SourceKPCompactTruncatedLocalEquation


set_option backward.privateInPublic true
@[expose] public section

/-! The actual global core weak equation with an exact compact localization. -/

namespace ArtinMatthews
open NumberField MeasureTheory Filter SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing Topology ContDiff BigOperators Classical InnerProductSpace
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "μ" => productVolume (InfinitePlace K)
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
local notation "T" => sourceKPCompactC2Core K hζ

theorem sourceKPCompactCore_test_pair_integrable (φ : T) (F : Y → ℂ) (hF : Continuous F) :
    Integrable (fun y => star (φ.val y)*F y) μY := by
  let : IsFiniteMeasureOnCompacts μY := sourceKPAutomorphicCompactHaar_finiteOnCompacts K hζ
  have hc : HasCompactSupport (fun y => star (φ.val y)) := φ.prop.2.1.comp_left (star_zero ℂ)
  exact (φ.prop.1.star.mul hF).integrable_of_hasCompactSupport hc.mul_right

theorem sourceKPCompactCore_weak_of_chart (w F : Y → ℂ) (hF : Continuous F)
    (hweak : ∀ (b : SourceKPFiniteLevelFiber K hζ) (ψ : h1Tests (InfinitePlace K) 2),
      (∫ x, productGradientPair ψ.val (sourceKPCompactChartPullback K hζ w b) x ∂μ) =
        ∫ x, star (ψ.val x)*sourceKPCompactChartPullback K hζ F b x ∂μ)
    (φ : T) :
    ∃ S : Set Y, IsCompact S ∧ ∀ v : T, (∀ y ∈ S, v.val =ᶠ[𝓝 y] w) →
      sourceKPCompactDirichletCore K hζ φ v = ∫ y, star (φ.val y)*F y ∂μY := by
  obtain ⟨I,b,p,η,hη⟩ := sourceKPCompactCore_sum_periodized_tests K hζ φ
  let ψ (i : Y) : T := sourceKPChartPeriodizationCore K hζ (b i) (η i).val
  let S : Set Y := ⋃ i ∈ I, tsupport (ψ i).val
  have hS : IsCompact S := I.isCompact_biUnion (fun i _ => (ψ i).prop.2.1)
  have hsum (y : Y) : φ.val y = ∑ i ∈ I, (ψ i).val y := by
    calc
      _ = ∑ i ∈ I, sourceKPChartPeriodizationGlobal K hζ (b i) (η i).val y := congrFun hη y
      _ = _ := Finset.sum_congr rfl (fun i _ => rfl)
  have hψ : φ = ∑ i ∈ I, ψ i := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    funext y
    simpa only [Finset.sum_apply] using hsum y
  refine ⟨S,hS,?_⟩
  intro v hv
  have htest (i : Y) (hi : i ∈ I) :
      sourceKPCompactDirichletCore K hζ (ψ i) v = ∫ y, star ((ψ i).val y)*F y ∂μY :=
    sourceKPPeriodizedWeakTest K hζ (b i) (p i) (η i) w F hF.measurable v
      (fun y hy => hv y (Set.mem_iUnion₂.mpr ⟨i,hi,hy⟩)) (fun ξ _ => hweak (b i) ξ)
  calc
    _ = ∑ i ∈ I, sourceKPCompactDirichletCore K hζ (ψ i) v := by
      rw [hψ]
      unfold sourceKPCompactDirichletCore
      rw [← integral_finsetSum _ (fun i _ => sourceKPCompactCorePairDensity_integrable K hζ (ψ i) v)]
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by
        simp only [sourceKPCompactCorePairDensity,map_sum,sum_inner]
    _ = ∑ i ∈ I, ∫ y, star ((ψ i).val y)*F y ∂μY :=
      Finset.sum_congr rfl htest
    _ = _ := by
      rw [← integral_finsetSum _ (fun i _ => sourceKPCompactCore_test_pair_integrable K hζ (ψ i) F hF)]
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by
        change (∑ i ∈ I, star ((ψ i).val y)*F y) = star (φ.val y)*F y
        rw [hsum y,star_sum,Finset.sum_mul]

theorem sourceKPCompactTruncated_weak_localization {T₀ : ℝ} (hT : 0 < T₀)
    {s : ℂ} (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (φ : T) :
    ∃ S : Set Y, IsCompact S ∧ ∀ v : T,
      (∀ y ∈ S, v.val =ᶠ[𝓝 y] sourceKPAutomorphicCompactTruncatedEisenstein K hζ T₀ s) →
      sourceKPCompactDirichletCore K hζ φ v =
        (InfinitePlace.nrComplexPlaces K : ℂ)*(1-4*s^2) *
          (∫ y, star (φ.val y)*sourceKPAutomorphicCompactTruncatedEisenstein K hζ T₀ s y ∂μY) -
          ∫ y, star (φ.val y)*sourceKPAutomorphicCompactCutoffDefect K hζ hT s y ∂μY := by
  let w := sourceKPAutomorphicCompactTruncatedEisenstein K hζ T₀ s
  let d := sourceKPAutomorphicCompactCutoffDefect K hζ hT s
  let lam : ℂ := (InfinitePlace.nrComplexPlaces K : ℂ)*(1-4*s^2)
  let F : Y → ℂ := lam • w-d
  have hw : Continuous w := sourceKPAutomorphicCompactTruncatedEisenstein_continuous K hζ hT hs
  have hd : Continuous d := by
    have hm : Continuous (fun x : Y => (s,x)) := continuous_const.prodMk continuous_id
    simpa only [Function.comp_def] using
      (sourceKPAutomorphicCompactCutoffDefect_joint_continuous K hζ hT).comp hm
  have hF : Continuous F := (hw.const_smul lam).sub hd
  have hweak (b : SourceKPFiniteLevelFiber K hζ) (ψ : h1Tests (InfinitePlace K) 2) :
      (∫ x, productGradientPair ψ.val (sourceKPCompactChartPullback K hζ w b) x ∂μ) =
        ∫ x, star (ψ.val x)*sourceKPCompactChartPullback K hζ F b x ∂μ := by
    have he : sourceKPCompactChartPullback K hζ F b =
        lam • sourceKPCompactChartPullback K hζ w b-sourceKPCompactChartPullback K hζ d b := by
      unfold F
      rw [sourceKPCompactChartPullback_sub,sourceKPCompactChartPullback_smul]
    have hiw := sourceKPProductTestPair_integrable K ψ
      (sourceKPCompactChartPullback_continuousOn K hζ w hw b)
    have hid := sourceKPProductTestPair_integrable K ψ
      (sourceKPCompactChartPullback_continuousOn K hζ d hd b)
    rw [sourceKPCompactChartPullback_truncated_gradient_equation K hζ hT hs b ψ,he,
      ← integral_const_mul,← integral_sub (hiw.const_mul lam) hid]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
      ring
  obtain ⟨S,hS,h⟩ := sourceKPCompactCore_weak_of_chart K hζ w F hF hweak φ
  refine ⟨S,hS,fun v hv => (h v hv).trans ?_⟩
  rw [← integral_const_mul,← integral_sub
    ((sourceKPCompactCore_test_pair_integrable K hζ φ w hw).const_mul lam)
    (sourceKPCompactCore_test_pair_integrable K hζ φ d hd)]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    simp only [F,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    ring

end
end ArtinMatthews
