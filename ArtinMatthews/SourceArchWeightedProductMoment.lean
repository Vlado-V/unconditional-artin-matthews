module

public import ArtinMatthews.SourceArchWeightedProduct
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap


set_option backward.privateInPublic true
@[expose] public section

/-! Compact height tests of the actual product Fourier kernel are holomorphic
on the absolute convergence half-plane. -/
namespace ArtinMatthews.SourceArchJacquet
open MeasureTheory Filter Metric
open scoped Topology BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "X" => (ι → ℝ)

def sourceArchWeightedProductMoment (ψ : ι → ℂ → ℂ) (a : ι → ℂ)
    (ν : Measure X) (S : Set X) (φ : X → ℂ) (s : ℂ) : ℂ :=
  ∫ y in S, φ y * sourceArchWeightedProduct ψ a s y ∂ν

theorem sourceArchWeightedProductMoment_hasDerivAt
    (ψ : ι → ℂ → ℂ) (hψ : ∀ i, Continuous (ψ i)) (hψ₁ : ∀ i x, ‖ψ i x‖ ≤ 1)
    (a : ι → ℂ) (ν : Measure X) (S : Set X) (hS : IsCompact S)
    (hμS : ν S ≠ ⊤) (hpos : ∀ y ∈ S, ∀ i, 0 < y i)
    (φ : X → ℂ) (hφ : Continuous φ) {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (sourceArchWeightedProductMoment ψ a ν S φ)
      (∫ y in S, φ y * sourceArchWeightedProductDerivative ψ a s y ∂ν) s := by
  let F := fun z y => φ y * sourceArchWeightedProduct ψ a z y
  let G := fun z y => φ y * sourceArchWeightedProductDerivative ψ a z y
  let B : Set (ℂ × X) := closedBall s (s.re/2) ×ˢ S
  let U : Set ℂ := ball s (s.re/2)
  let μS := ν.restrict S
  let : IsFiniteMeasure μS := ⟨by simpa only [μS,Measure.restrict_apply_univ] using hμS.lt_top⟩
  have hB : IsCompact B := (isCompact_closedBall s (s.re/2)).prod hS
  have hreal {z : ℂ} (hz : z ∈ closedBall s (s.re/2)) : 0 < z.re := by
    have hd : s.re-z.re ≤ ‖s-z‖ := by simpa only [Complex.sub_re] using Complex.re_le_norm (s-z)
    have hn : ‖s-z‖ ≤ s.re/2 := by simpa only [mem_closedBall,dist_eq_norm,norm_sub_rev] using hz
    linarith
  have hGc : ContinuousOn (fun p : ℂ × X => G p.1 p.2) B := by
    intro p hp
    exact ((hφ.comp continuous_snd).continuousAt.mul
      (sourceArchWeightedProductDerivative_continuousAt ψ hψ hψ₁ a p
        (hreal hp.1) (hpos p.2 hp.2))).continuousWithinAt
  obtain ⟨M,hM⟩ := hB.exists_bound_of_continuousOn hGc
  have hFc (z : ℂ) (hz : 0 < z.re) : ContinuousOn (F z) S := by
    intro y hy
    have hc : ContinuousAt (fun y => sourceArchWeightedProduct ψ a z y) y := by
      have hpair : Continuous (fun y : X => (z,y)) := continuous_const.prodMk continuous_id
      exact (sourceArchWeightedProduct_continuousAt ψ hψ hψ₁ a (z,y) hz
        (hpos y hy)).comp hpair.continuousAt
    exact (hφ.continuousAt.mul hc).continuousWithinAt
  have hGcs : ContinuousOn (G s) S := by
    intro y hy
    have hpair : Continuous (fun y : X => (s,y)) := continuous_const.prodMk continuous_id
    exact (hφ.continuousAt.mul
      ((sourceArchWeightedProductDerivative_continuousAt ψ hψ hψ₁ a (s,y) hs
        (hpos y hy)).comp hpair.continuousAt)).continuousWithinAt
  have hFmeas : ∀ᶠ z in 𝓝 s, AEStronglyMeasurable (F z) μS := by
    filter_upwards [show U ∈ 𝓝 s from ball_mem_nhds s (half_pos hs)] with z hz
    exact (hFc z (hreal (ball_subset_closedBall hz))).aestronglyMeasurable hS.measurableSet
  have hFi : Integrable (F s) μS :=
    (hFc s hs).integrableOn_of_subset_isCompact hS hS.measurableSet Set.Subset.rfl hμS
  have hGi : AEStronglyMeasurable (G s) μS :=
    hGcs.aestronglyMeasurable hS.measurableSet
  have hbound : ∀ᵐ y ∂μS, ∀ z ∈ U, ‖G z y‖ ≤ M := by
    filter_upwards [ae_restrict_mem hS.measurableSet] with y hy z hz
    exact hM (z,y) ⟨ball_subset_closedBall hz,hy⟩
  have hd : ∀ᵐ y ∂μS, ∀ z ∈ U, HasDerivAt (fun w => F w y) (G z y) z := by
    filter_upwards [ae_restrict_mem hS.measurableSet] with y hy z hz
    exact (sourceArchWeightedProduct_hasDerivAt ψ hψ hψ₁ a
      (hreal (ball_subset_closedBall hz)) y (hpos y hy)).const_mul (φ y)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℂ) (μ := μS) (x₀ := s) (s := U) (F := F) (F' := G)
    (bound := fun _ => M) (ball_mem_nhds s (half_pos hs)) hFmeas hFi hGi hbound
    (integrable_const M) hd).2

theorem sourceArchWeightedProductMoment_analyticOnNhd
    (ψ : ι → ℂ → ℂ) (hψ : ∀ i, Continuous (ψ i)) (hψ₁ : ∀ i x, ‖ψ i x‖ ≤ 1)
    (a : ι → ℂ) (ν : Measure X) (S : Set X) (hS : IsCompact S)
    (hμS : ν S ≠ ⊤) (hpos : ∀ y ∈ S, ∀ i, 0 < y i)
    (φ : X → ℂ) (hφ : Continuous φ) :
    AnalyticOnNhd ℂ (sourceArchWeightedProductMoment ψ a ν S φ) {z : ℂ | 0 < z.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro s hs
  exact (sourceArchWeightedProductMoment_hasDerivAt ψ hψ hψ₁ a ν S hS hμS hpos φ hφ hs).differentiableAt.differentiableWithinAt

end
end ArtinMatthews.SourceArchJacquet
