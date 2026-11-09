module

public import ArtinMatthews.SpectralKLCompactInverse
public import ArtinMatthews.SpectralBesselOrderUniform


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory Filter OAI.CubicEisenstein
open scoped Topology
noncomputable section

def spectralKLCompactOrderIntegrand (g : ℝ → ℂ) (ν : ℂ) (x : ℝ) : ℂ :=
  schlafliBesselK ν x * spectralKLPhysicalCompactDiv g x

def spectralKLCompactOrderTransform (g : ℝ → ℂ) (ν : ℂ) : ℂ :=
  ∫ x : ℝ, spectralKLCompactOrderIntegrand g ν x

def spectralKLCompactOrderDerivativeIntegrand (g : ℝ → ℂ) (ν : ℂ) (x : ℝ) : ℂ :=
  ((1 / 2 : ℂ) * ∫ u : ℝ, spectralKOrderDerivativeKernel ν x u) * spectralKLPhysicalCompactDiv g x

theorem spectralKLCompactOrderIntegrand_continuous (g : ℝ → ℂ) (hg : Continuous g)
    (hp : tsupport g ⊆ Ioi (0 : ℝ)) (ν : ℂ) :
    Continuous (spectralKLCompactOrderIntegrand g ν) := by
  have hdiv := spectralKLPhysicalCompactDiv_continuous g hg hp
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ tsupport g
  · exact (schlafliBesselK_hasDerivAt ν x (hp hx)).continuousAt.mul hdiv.continuousAt
  · have hz := notMem_tsupport_iff_eventuallyEq.mp hx
    have heq : spectralKLCompactOrderIntegrand g ν =ᶠ[𝓝 x] (0 : ℝ → ℂ) := by
      filter_upwards [hz] with y hy
      simp [spectralKLCompactOrderIntegrand, spectralKLPhysicalCompactDiv, hy]
    exact continuousAt_const.congr heq.symm

theorem spectralKLCompactOrderIntegrand_compact (g : ℝ → ℂ) (hc : HasCompactSupport g) (ν : ℂ) :
    HasCompactSupport (spectralKLCompactOrderIntegrand g ν) := by
  apply hc.mono'
  intro x hx
  by_contra hg
  have hg0 := image_eq_zero_of_notMem_tsupport hg
  exact hx (by simp [spectralKLCompactOrderIntegrand, spectralKLPhysicalCompactDiv, hg0])

theorem spectralKLCompactOrderIntegrand_integrable (g : ℝ → ℂ) (hg : Continuous g)
    (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi (0 : ℝ)) (ν : ℂ) :
    Integrable (spectralKLCompactOrderIntegrand g ν) :=
  (spectralKLCompactOrderIntegrand_continuous g hg hp ν).integrable_of_hasCompactSupport
    (spectralKLCompactOrderIntegrand_compact g hc ν)

theorem spectralKLCompactOrderDerivativeIntegrand_measurable (g : ℝ → ℂ) (hg : Continuous g)
    (hp : tsupport g ⊆ Ioi (0 : ℝ)) (ν : ℂ) :
    StronglyMeasurable (spectralKLCompactOrderDerivativeIntegrand g ν) := by
  have hk : Continuous (fun p : ℝ × ℝ => spectralKOrderDerivativeKernel ν p.1 p.2) := by
    unfold spectralKOrderDerivativeKernel spectralKLogKernel
    fun_prop
  exact (stronglyMeasurable_const.mul hk.stronglyMeasurable.integral_prod_right').mul
    (spectralKLPhysicalCompactDiv_continuous g hg hp).stronglyMeasurable

theorem spectralKLCompactOrderIntegrand_hasDerivAt (g : ℝ → ℂ)
    (hp : tsupport g ⊆ Ioi (0 : ℝ)) (ν : ℂ) (x : ℝ) :
    HasDerivAt (fun μ => spectralKLCompactOrderIntegrand g μ x)
      (spectralKLCompactOrderDerivativeIntegrand g ν x) ν := by
  by_cases hg : g x = 0
  · simpa only [spectralKLCompactOrderIntegrand, spectralKLCompactOrderDerivativeIntegrand,
      spectralKLPhysicalCompactDiv, hg, zero_div, mul_zero] using hasDerivAt_const ν (0 : ℂ)
  · exact (schlafliBesselK_order_hasDerivAt ν (hp (subset_tsupport g hg))).mul_const _

theorem spectralKLCompactOrderTransform_hasDerivAt (g : ℝ → ℂ) (hg : Continuous g)
    (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi (0 : ℝ)) (ν : ℂ) :
    HasDerivAt (spectralKLCompactOrderTransform g)
      (∫ x : ℝ, spectralKLCompactOrderDerivativeIntegrand g ν x) ν := by
  obtain ⟨a, ha, hasupport⟩ := spectral_compact_positive_lower_bound g hc hp
  have hbound (μ : ℂ) (hμ : μ ∈ Metric.ball ν 1) (x : ℝ) :
      ‖spectralKLCompactOrderDerivativeIntegrand g μ x‖ ≤
        spectralKOrderUniformBound ν a * ‖spectralKLPhysicalCompactDiv g x‖ := by
    by_cases hgx : g x = 0
    · simp [spectralKLCompactOrderDerivativeIntegrand, spectralKLPhysicalCompactDiv, hgx]
    · have hx := hp (subset_tsupport g hgx)
      unfold spectralKLCompactOrderDerivativeIntegrand
      rw [norm_mul, ← (schlafliBesselK_order_hasDerivAt μ hx).deriv]
      exact mul_le_mul_of_nonneg_right
        (schlafliBesselK_order_deriv_uniform μ ν a x ha (hasupport x (subset_tsupport g hgx)) hμ)
        (norm_nonneg _)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun μ x => spectralKLCompactOrderIntegrand g μ x)
    (F' := fun μ x => spectralKLCompactOrderDerivativeIntegrand g μ x)
    (μ := volume) (s := Metric.ball ν 1) (Metric.ball_mem_nhds ν (by norm_num))
    (Eventually.of_forall fun μ => (spectralKLCompactOrderIntegrand_continuous g hg hp μ).aestronglyMeasurable)
    (spectralKLCompactOrderIntegrand_integrable g hg hc hp ν)
    (spectralKLCompactOrderDerivativeIntegrand_measurable g hg hp ν).aestronglyMeasurable
    (ae_of_all _ fun x μ hμ => hbound μ hμ x)
    ((spectralKLPhysicalCompactDiv_integrable g hg hc hp).norm.const_mul _)
    (ae_of_all _ fun x μ _ => spectralKLCompactOrderIntegrand_hasDerivAt g hp μ x)).2

theorem spectralKLCompactOrderTransform_entire (g : ℝ → ℂ) (hg : Continuous g)
    (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi (0 : ℝ)) :
    Differentiable ℂ (spectralKLCompactOrderTransform g) :=
  fun ν => (spectralKLCompactOrderTransform_hasDerivAt g hg hc hp ν).differentiableAt

theorem spectralKLCompactOrderTransform_imaginary (g : ℝ → ℂ)
    (hp : tsupport g ⊆ Ioi (0 : ℝ)) (t : ℝ) :
    spectralKLCompactOrderTransform g ((t : ℂ) * Complex.I) = spectralKLPhysicalAnalysisIntegral g t := by
  unfold spectralKLCompactOrderTransform spectralKLPhysicalAnalysisIntegral
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : 0 < x
  · simp only [spectralKLCompactOrderIntegrand, schlafliBesselK_imaginary_eq_realKernel t hx]
  · have hg : g x = 0 := image_eq_zero_of_notMem_tsupport (fun hs => hx (hp hs))
    simp [spectralKLCompactOrderIntegrand, spectralKLPhysicalCompactDiv, hg]

theorem spectralKLCompactOrderTransform_even (g : ℝ → ℂ)
    (hp : tsupport g ⊆ Ioi (0 : ℝ)) (ν : ℂ) :
    spectralKLCompactOrderTransform g (-ν) = spectralKLCompactOrderTransform g ν := by
  unfold spectralKLCompactOrderTransform
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : 0 < x
  · have hK : schlafliBesselK (-ν) x = schlafliBesselK ν x := by
      rw [schlafliBesselK_cosh_integral (-ν) hx, schlafliBesselK_cosh_integral ν hx]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u _
      simp [spectralKCoshKernel, neg_mul, Complex.cosh_neg]
    simp only [spectralKLCompactOrderIntegrand, hK]
  · have hg : g x = 0 := image_eq_zero_of_notMem_tsupport (fun hs => hx (hp hs))
    simp [spectralKLCompactOrderIntegrand, spectralKLPhysicalCompactDiv, hg]

end
end ArtinMatthews
