module

public import ArtinMatthews.SourceKPCompactTruncatedChart
public import ArtinMatthews.SourceKPAdelicEisensteinGradientEquation
public import ArtinMatthews.SourceKPAutomorphicDefectContinuity
public import ArtinMatthews.SourceHyperbolicNativeGreen


set_option backward.privateInPublic true
@[expose] public section

/-! The exact weak inhomogeneous equation on every actual product chart. -/

namespace ArtinMatthews
open NumberField MeasureTheory Filter SourceArchJacquet SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing Topology ContDiff BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "P" => ProductSpace (InfinitePlace K)
local notation "Ω" => productUpper (InfinitePlace K)
local notation "μ" => productVolume (InfinitePlace K)

theorem sourceKPProductTestPair_integrable (φ : h1Tests (InfinitePlace K) 2)
    {f : P → ℂ} (hf : ContinuousOn f Ω) :
    Integrable (fun p => star (φ.val p)*f p) μ := by
  let g := fun p => star (φ.val p)*f p
  have hs : tsupport g ⊆ tsupport φ.val :=
    tsupport_mul_subset_left.trans (tsupport_comp_subset (g := star) (star_zero ℂ) φ.val)
  have hc : Continuous g := by
    apply continuous_of_tsupport
    intro p hp
    have hpU := φ.prop.2.2 (hs hp)
    exact φ.prop.1.continuous.continuousAt.star.mul
      ((hf p hpU).continuousAt ((productUpper_isOpen (InfinitePlace K)).mem_nhds hpU))
  exact memLp_one_iff_integrable.mp
    (h1_compact_memLp hc (φ.prop.2.1.of_isClosed_subset isClosed_closure hs)
      (hs.trans φ.prop.2.2) 1)

theorem sourceKPCompactChartPullback_defect_continuousOn {T : ℝ} (hT : 0 < T)
    (s : ℂ) (b : SourceKPFiniteLevelFiber K hζ) :
    ContinuousOn (sourceKPCompactChartPullback K hζ
      (sourceKPAutomorphicCompactCutoffDefect K hζ hT s) b) Ω := by
  apply sourceKPCompactChartPullback_continuousOn
  have hm : Continuous (fun y : SourceKPAutomorphicCompactLevel K hζ => (s,y)) :=
    continuous_const.prodMk continuous_id
  simpa only [Function.comp_def] using
    (sourceKPAutomorphicCompactCutoffDefect_joint_continuous K hζ hT).comp hm

theorem sourceKPCompactChartPullback_cutoff_gradient_equation {T : ℝ} (hT : 0 < T)
    (s : ℂ) (b : SourceKPFiniteLevelFiber K hζ) (φ : h1Tests (InfinitePlace K) 2) :
    (∫ p, productGradientPair φ.val (sourceKPCompactChartPullback K hζ
      (sourceKPAutomorphicCompactCutoffEisenstein K hζ T s) b) p ∂μ) =
      (InfinitePlace.nrComplexPlaces K : ℂ)*(1-4*s^2) *
        (∫ p, star (φ.val p)*sourceKPCompactChartPullback K hζ
          (sourceKPAutomorphicCompactCutoffEisenstein K hζ T s) b p ∂μ) +
        ∫ p, star (φ.val p)*sourceKPCompactChartPullback K hζ
          (sourceKPAutomorphicCompactCutoffDefect K hζ hT s) b p ∂μ := by
  obtain ⟨qf,rfl⟩ := Quotient.mk_surjective b
  let Q := sourceKPAdelicCutoffEisensteinProductChart K hζ T s (1,qf)
  let D := sourceKPCompactChartPullback K hζ (sourceKPAutomorphicCompactCutoffDefect K hζ hT s)
    (QuotientGroup.mk qf)
  let lam : ℂ := (InfinitePlace.nrComplexPlaces K : ℂ)*(1-4*s^2)
  have hQ : ContDiffOn ℝ 2 Q Ω := by
    intro p hp
    exact ((sourceKPAdelicCutoffEisensteinProductChart_contDiffAt K hζ hT s (1,qf) p
      (fun v => productUpper_pos hp v)).of_le (by simp)).contDiffWithinAt
  have hD : ContinuousOn D Ω := sourceKPCompactChartPullback_defect_continuousOn K hζ hT s _
  have he : sourceKPCompactChartPullback K hζ
      (sourceKPAutomorphicCompactCutoffEisenstein K hζ T s) (QuotientGroup.mk qf) = Q :=
    sourceKPCompactChartPullback_cutoff K hζ T s qf
  rw [he,product_native_green_on hQ φ.prop.1.contDiffOn φ.prop.2.1 φ.prop.2.2]
  change (∫ p, star (φ.val p)*sourceArchProductCoordinateLaplacian Q p ∂μ) =
    lam*(∫ p, star (φ.val p)*Q p ∂μ) + ∫ p, star (φ.val p)*D p ∂μ
  rw [← integral_const_mul,← integral_add ((sourceKPProductTestPair_integrable K φ hQ.continuousOn).const_mul lam)
    (sourceKPProductTestPair_integrable K φ hD)]
  apply integral_congr_ae
  filter_upwards [productVolume_ae_upper (ι := InfinitePlace K)] with p hp
  have h := sourceKPAdelicCutoffEisensteinProductChart_compact_defect K hζ hT s (1,qf) p
    (fun v => productUpper_pos hp v)
  rw [← sourceKPUpperToCompact_product_point K hζ qf p hp] at h
  have hDval : D p = sourceKPAutomorphicCompactCutoffDefect K hζ hT s
      (sourceKPUpperToCompact K hζ (QuotientGroup.mk qf) (sourceKPArchEuclideanUpperMap K p)) :=
    sourceKPCompactChartPullback_of_positive K hζ _ (QuotientGroup.mk qf) p hp
  change sourceArchProductCoordinateLaplacian Q p-lam*Q p = _ at h
  rw [← hDval] at h
  rw [sub_eq_iff_eq_add.mp h]
  ring

theorem sourceKPCompactChartPullback_truncated_gradient_equation {T : ℝ} (hT : 0 < T)
    {s : ℂ} (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (b : SourceKPFiniteLevelFiber K hζ) (φ : h1Tests (InfinitePlace K) 2) :
    (∫ p, productGradientPair φ.val (sourceKPCompactChartPullback K hζ
      (sourceKPAutomorphicCompactTruncatedEisenstein K hζ T s) b) p ∂μ) =
      (InfinitePlace.nrComplexPlaces K : ℂ)*(1-4*s^2) *
        (∫ p, star (φ.val p)*sourceKPCompactChartPullback K hζ
          (sourceKPAutomorphicCompactTruncatedEisenstein K hζ T s) b p ∂μ) -
        ∫ p, star (φ.val p)*sourceKPCompactChartPullback K hζ
          (sourceKPAutomorphicCompactCutoffDefect K hζ hT s) b p ∂μ := by
  obtain ⟨qf,rfl⟩ := Quotient.mk_surjective b
  let E := sourceKPAdelicEisensteinProductChart K hζ s (1,qf)
  let Q := sourceKPAdelicCutoffEisensteinProductChart K hζ T s (1,qf)
  have hE := sourceKPAdelicEisensteinProductChart_contDiffOn K hζ hs (1,qf)
  have hQ : ContDiffOn ℝ 2 Q Ω := by
    intro p hp
    exact ((sourceKPAdelicCutoffEisensteinProductChart_contDiffAt K hζ hT s (1,qf) p
      (fun v => productUpper_pos hp v)).of_le (by simp)).contDiffWithinAt
  have hEg := sourceKPAdelicEisensteinProductChart_gradient_eigen K hζ hs (1,qf)
    φ.prop.1.contDiffOn φ.prop.2.1 φ.prop.2.2
  have hQg := sourceKPCompactChartPullback_cutoff_gradient_equation K hζ hT s
    (QuotientGroup.mk qf) φ
  rw [sourceKPCompactChartPullback_cutoff] at hQg
  rw [sourceKPCompactChartPullback_truncated]
  have hPair : (fun p => productGradientPair φ.val (E-Q) p) =ᵐ[μ]
      fun p => productGradientPair φ.val E p-productGradientPair φ.val Q p := by
    filter_upwards [productVolume_ae_upper (ι := InfinitePlace K)] with p hp
    have hn := (productUpper_isOpen (InfinitePlace K)).mem_nhds hp
    have hEd : DifferentiableAt ℝ E p := ((hE p hp).contDiffAt hn).differentiableAt (by norm_num)
    have hQd := ((hQ p hp).contDiffAt hn).differentiableAt (by norm_num)
    have hd : fderiv ℝ (E-Q) p = fderiv ℝ E p-fderiv ℝ Q p := fderiv_sub hEd hQd
    simp only [productGradientPair,productPartial,hd,ContinuousLinearMap.sub_apply,
      mul_sub,Finset.sum_sub_distrib]
  rw [integral_congr_ae hPair,integral_sub
    (sourceKPAdelicEisensteinProductChart_gradient_integrable K hζ hs (1,qf)
      φ.prop.1.contDiffOn φ.prop.2.1 φ.prop.2.2)
    (productGradientPair_integrable (fun p hp => (hQ p hp).contDiffAt
      ((productUpper_isOpen (InfinitePlace K)).mem_nhds hp)) φ.prop.1 φ.prop.2.1 φ.prop.2.2),
    hEg,hQg]
  simp only [Pi.sub_apply,mul_sub]
  rw [integral_sub (sourceKPProductTestPair_integrable K φ hE.continuousOn)
    (sourceKPProductTestPair_integrable K φ hQ.continuousOn)]
  ring

end
end ArtinMatthews
