module

public import ArtinMatthews.SpectralBesselOrderUniform
public import ArtinMatthews.SpectralCuspBesselTransform
public import ArtinMatthews.SpectralCuspPositiveTestWeights
public import Mathlib.MeasureTheory.Integral.Prod


set_option backward.privateInPublic true
@[expose] public section

/-! The actual compact height integrand and its order derivative have
measurable, integrable majorants on every complex-order neighborhood. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace ArtinMatthews

def cuspBesselHeightWeight (ρ : ℝ → ℝ) (y : ℝ) : ℂ :=
  ((ρ y/y^2 : ℝ) : ℂ)*(Real.sqrt y : ℂ)

theorem cuspBesselHeightWeight_continuous (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) : Continuous (cuspBesselHeightWeight ρ) := by
  unfold cuspBesselHeightWeight
  exact (Complex.continuous_ofReal.comp (spectralPositiveTest_div_pow_contDiff ρ hρ hpρ 2).continuous).mul
    (Complex.continuous_ofReal.comp Real.continuous_sqrt)

theorem cuspBesselHeightWeight_compact (ρ : ℝ → ℝ) (hcρ : HasCompactSupport ρ) :
    HasCompactSupport (cuspBesselHeightWeight ρ) := by
  apply hcρ.mono'
  intro y hy
  by_contra hρ
  exact hy (by simp [cuspBesselHeightWeight,image_eq_zero_of_notMem_tsupport hρ])

theorem cuspBesselTransformIntegrand_eq_weight (ν : ℂ) (q : ℝ) (ρ : ℝ → ℝ) (y : ℝ) :
    cuspBesselTransformIntegrand ν q ρ y =
      cuspBesselHeightWeight ρ y*OAI.CubicEisenstein.schlafliBesselK ν (q*y) := by
  unfold cuspBesselTransformIntegrand cuspBesselKernel cuspBesselHeightWeight
  ring

def cuspBesselOrderDerivativeIntegrand (ν : ℂ) (q : ℝ) (ρ : ℝ → ℝ) (y : ℝ) : ℂ :=
  cuspBesselHeightWeight ρ y*((1/2 : ℂ)*∫ u : ℝ,spectralKOrderDerivativeKernel ν (q*y) u)

theorem cuspBesselOrderDerivativeIntegrand_stronglyMeasurable
    (ν : ℂ) (q : ℝ) (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) :
    StronglyMeasurable (cuspBesselOrderDerivativeIntegrand ν q ρ) := by
  have hc : Continuous (fun p : ℝ × ℝ => spectralKOrderDerivativeKernel ν (q*p.1) p.2) := by
    unfold spectralKOrderDerivativeKernel spectralKLogKernel
    fun_prop
  have hi : StronglyMeasurable (fun y => ∫ u : ℝ,spectralKOrderDerivativeKernel ν (q*y) u) :=
    hc.stronglyMeasurable.integral_prod_right'
  exact (cuspBesselHeightWeight_continuous ρ hρ hpρ).stronglyMeasurable.mul
    (stronglyMeasurable_const.mul hi)

theorem cuspBesselTransformIntegrand_order_hasDerivAt (ν : ℂ) {q Y : ℝ}
    (hq : 0 < q) (hY : 0 < Y) (ρ : ℝ → ℝ) (hsρ : tsupport ρ ⊆ Ioi Y) (y : ℝ) :
    HasDerivAt (fun μ => cuspBesselTransformIntegrand μ q ρ y)
      (cuspBesselOrderDerivativeIntegrand ν q ρ y) ν := by
  have he : (fun μ => cuspBesselTransformIntegrand μ q ρ y) =
      fun μ => cuspBesselHeightWeight ρ y*OAI.CubicEisenstein.schlafliBesselK μ (q*y) :=
    funext (fun μ => cuspBesselTransformIntegrand_eq_weight μ q ρ y)
  rw [he]
  by_cases hy : y ∈ tsupport ρ
  · have hy0 : 0 < y := hY.trans (hsρ hy)
    exact (schlafliBesselK_order_hasDerivAt ν (mul_pos hq hy0)).const_mul (cuspBesselHeightWeight ρ y)
  · have hz : ρ y = 0 := image_eq_zero_of_notMem_tsupport hy
    simpa only [cuspBesselHeightWeight,cuspBesselOrderDerivativeIntegrand,hz,zero_div,
      Complex.ofReal_zero,zero_mul] using hasDerivAt_const ν (0 : ℂ)

theorem cuspBesselOrderDerivativeIntegrand_bound (ν ν₀ : ℂ) {q Y : ℝ}
    (hq : 0 < q) (hY : 0 < Y) (ρ : ℝ → ℝ) (hsρ : tsupport ρ ⊆ Ioi Y)
    (hν : ν ∈ Metric.ball ν₀ 1) (y : ℝ) :
    ‖cuspBesselOrderDerivativeIntegrand ν q ρ y‖ ≤
      ‖cuspBesselHeightWeight ρ y‖*spectralKOrderUniformBound ν₀ (q*Y) := by
  by_cases hy : y ∈ tsupport ρ
  · have hy0 : 0 < y := hY.trans (hsρ hy)
    have hqy : q*Y ≤ q*y := mul_le_mul_of_nonneg_left (hsρ hy).le hq.le
    have h := schlafliBesselK_order_deriv_uniform ν ν₀ (q*Y) (q*y) (mul_pos hq hY) hqy hν
    rw [(schlafliBesselK_order_hasDerivAt ν (mul_pos hq hy0)).deriv] at h
    unfold cuspBesselOrderDerivativeIntegrand
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left h (norm_nonneg _)
  · have hz : ρ y = 0 := image_eq_zero_of_notMem_tsupport hy
    simp only [cuspBesselOrderDerivativeIntegrand,cuspBesselHeightWeight,hz,zero_div,
      Complex.ofReal_zero,zero_mul,norm_zero]
    exact le_rfl

theorem cuspBesselOrderDerivative_majorant_integrable (ν : ℂ) (q Y : ℝ)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) :
    Integrable (fun y => ‖cuspBesselHeightWeight ρ y‖*spectralKOrderUniformBound ν (q*Y)) :=
  ((cuspBesselHeightWeight_continuous ρ hρ hpρ).integrable_of_hasCompactSupport
    (cuspBesselHeightWeight_compact ρ hcρ)).norm.mul_const _

end ArtinMatthews
