module

public import ArtinMatthews.SourceLocalAdditivePower
public import ArtinMatthews.SourceFiniteWindowWeight
public import ArtinMatthews.SourceFiniteIntertwiningHeight
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral


set_option backward.privateInPublic true
@[expose] public section

/-! Holomorphy of the literal finite-window intertwining integral in the positive half-plane. -/

namespace ArtinMatthews

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped NumberField AdeleRing BigOperators

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance finiteWindowHolomorphicMeasurable : MeasurableSpace 𝔸ᶠ[K] := borel 𝔸ᶠ[K]
local instance finiteWindowHolomorphicBorel : BorelSpace 𝔸ᶠ[K] := ⟨rfl⟩

theorem sourceKPFiniteIntertwiningKernel_continuous (s : ℂ)
    (g : SourceKPFiniteAdeleProjective K hζ) :
    Continuous (sourceKPFiniteIntertwiningKernel K hζ s g) := by
  rw [show sourceKPFiniteIntertwiningKernel K hζ s g =
    fun y => sourceKPAdelicIntertwiningKernel K hζ s (1, g) (0, y) from
    funext (sourceKPFiniteIntertwiningKernel_eq_adelic K hζ s g)]
  exact (sourceKPAdelicIntertwiningKernel_continuous K hζ s (1, g)).comp
    (continuous_const.prodMk continuous_id)

theorem sourceKPFiniteIntertwiningKernel_entire (g : SourceKPFiniteAdeleProjective K hζ)
    (y : 𝔸ᶠ[K]) : Differentiable ℂ (fun s => sourceKPFiniteIntertwiningKernel K hζ s g y) := by
  simp_rw [sourceKPFiniteIntertwiningKernel_eq_adelic K hζ]
  exact sourceKPAdelicIntertwiningKernel_entire K hζ (1, g) (0, y)

theorem sourceKPFiniteIntertwiningKernel_window_integrable {s : ℂ} (hs : 0 < s.re)
    (g : SourceKPFiniteAdeleProjective K hζ) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IntegrableOn (sourceKPFiniteIntertwiningKernel K hζ s g) (sourceKPFiniteWindow K S)
      (sourceKPFiniteStandardHaar K) := by
  obtain ⟨C, _hC, hb⟩ := sourceKPFiniteIntertwiningKernel_window_bound K hζ g S
  have hp : IntegrableOn (sourceKPFiniteWindowPower K S (2 * s.re + 1))
      (sourceKPFiniteWindow K S) (sourceKPFiniteStandardHaar K) :=
    sourceKPFiniteWindow_prod_integrableOn K (fun _ x => (max 1 ‖x‖) ^ (-(2 * s.re + 1)))
      (fun P => sourceKPLocalAdditivePower_integrable K P (by linarith)) S
  apply (hp.const_mul (C ^ (s.re + 1 / 2))).mono'
    (sourceKPFiniteIntertwiningKernel_continuous K hζ s g).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (sourceKPFiniteWindow_isClosed K S).measurableSet] with y hy
  exact hb s hs y hy

theorem sourceKPFiniteIntertwiningKernel_window_mul_integrable {s : ℂ} (hs : 0 < s.re)
    (g : SourceKPFiniteAdeleProjective K hζ) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φ : 𝔸ᶠ[K] → ℂ) (hφ : Measurable φ) (B : ℝ)
    (hφB : ∀ y ∈ sourceKPFiniteWindow K S, ‖φ y‖ ≤ B) :
    IntegrableOn (fun y => φ y * sourceKPFiniteIntertwiningKernel K hζ s g y)
      (sourceKPFiniteWindow K S) (sourceKPFiniteStandardHaar K) := by
  have hi := sourceKPFiniteIntertwiningKernel_window_integrable K hζ hs g S
  apply (hi.norm.const_mul B).mono' (hφ.aestronglyMeasurable.mul hi.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem (sourceKPFiniteWindow_isClosed K S).measurableSet] with y hy
  change ‖φ y * sourceKPFiniteIntertwiningKernel K hζ s g y‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hφB y hy) (norm_nonneg _)

private theorem finiteIntertwiningKernel_deriv_measurable
    (μ : Measure 𝔸ᶠ[K]) (s : ℂ) (g : SourceKPFiniteAdeleProjective K hζ) :
    AEStronglyMeasurable (fun y : 𝔸ᶠ[K] =>
      deriv (fun z : ℂ => sourceKPFiniteIntertwiningKernel K hζ z g y) s) μ := by
  apply aestronglyMeasurable_of_tendsto_ae (𝓝[≠] (0 : ℂ))
    (f := fun (u : ℂ) (y : 𝔸ᶠ[K]) => u⁻¹ • (sourceKPFiniteIntertwiningKernel K hζ (s + u) g y -
      sourceKPFiniteIntertwiningKernel K hζ s g y))
  · intro u
    exact (((sourceKPFiniteIntertwiningKernel_continuous K hζ (s + u) g).sub
      (sourceKPFiniteIntertwiningKernel_continuous K hζ s g)).aestronglyMeasurable).const_smul u⁻¹
  · exact Filter.Eventually.of_forall (fun y =>
      (sourceKPFiniteIntertwiningKernel_entire K hζ g y s).hasDerivAt.tendsto_slope_zero)

theorem sourceKPFiniteWindowWeightedIntertwiner_hasDerivAt {s : ℂ} (hs : 0 < s.re)
    (g : SourceKPFiniteAdeleProjective K hζ) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φ : 𝔸ᶠ[K] → ℂ) (hφ : Measurable φ) (B : ℝ) (hB : 0 ≤ B)
    (hφB : ∀ y ∈ sourceKPFiniteWindow K S, ‖φ y‖ ≤ B) :
    HasDerivAt (fun z => sourceKPFiniteWindowIntegral K
      (fun y => φ y * sourceKPFiniteIntertwiningKernel K hζ z g y) S)
      (∫ y in sourceKPFiniteWindow K S,
        φ y * deriv (fun z => sourceKPFiniteIntertwiningKernel K hζ z g y) s
          ∂sourceKPFiniteStandardHaar K) s := by
  let μ := (sourceKPFiniteStandardHaar K).restrict (sourceKPFiniteWindow K S)
  let δ : ℝ := s.re / 4
  let a : ℝ := s.re - 2 * δ
  let b : ℝ := s.re + 2 * δ
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  have ha : 0 < (a : ℂ).re := by simp only [Complex.ofReal_re, a, δ]; linarith
  have hb : 0 < (b : ℂ).re := by simp only [Complex.ofReal_re, b, δ]; linarith
  let bound (y : 𝔸ᶠ[K]) := B * (δ⁻¹ *
    (‖sourceKPFiniteIntertwiningKernel K hζ (a : ℂ) g y‖ +
      ‖sourceKPFiniteIntertwiningKernel K hζ (b : ℂ) g y‖))
  have hbound : Integrable bound μ :=
    (((sourceKPFiniteIntertwiningKernel_window_integrable K hζ ha g S).norm.add
      (sourceKPFiniteIntertwiningKernel_window_integrable K hζ hb g S).norm).const_mul (δ⁻¹)).const_mul B
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z y => φ y * sourceKPFiniteIntertwiningKernel K hζ z g y)
    (F' := fun z y => φ y * deriv (fun w => sourceKPFiniteIntertwiningKernel K hζ w g y) z)
    (s := Metric.ball s δ) (bound := bound)
    (Metric.ball_mem_nhds s hδ) _
    (sourceKPFiniteIntertwiningKernel_window_mul_integrable K hζ hs g S φ hφ B hφB)
    (hφ.aestronglyMeasurable.mul (finiteIntertwiningKernel_deriv_measurable K hζ μ s g))
    _ hbound _).2
  · exact Filter.Eventually.of_forall (fun z =>
      hφ.aestronglyMeasurable.mul
        (sourceKPFiniteIntertwiningKernel_continuous K hζ z g).aestronglyMeasurable)
  · filter_upwards [ae_restrict_mem (sourceKPFiniteWindow_isClosed K S).measurableSet] with y hy
    intro z hz
    have hre : |z.re - s.re| < δ := lt_of_le_of_lt
      (by simpa only [Complex.sub_re] using Complex.abs_re_le_norm (z - s))
      (by simpa only [Metric.mem_ball, dist_eq_norm] using hz)
    have hstrip : a + δ ≤ z.re ∧ z.re ≤ b - δ := by
      dsimp only [a, b]
      constructor <;> linarith [abs_lt.mp hre]
    have hderiv : ‖deriv (fun w => sourceKPFiniteIntertwiningKernel K hζ w g y) z‖ ≤
        δ⁻¹ * (‖sourceKPFiniteIntertwiningKernel K hζ (a : ℂ) g y‖ +
          ‖sourceKPFiniteIntertwiningKernel K hζ (b : ℂ) g y‖) := by
      simpa only [sourceKPFiniteIntertwiningKernel_eq_adelic K hζ] using
        sourceKPAdelicIntertwiningKernel_deriv_bound K hζ a b δ hδ z hstrip (1, g) (0, y)
    rw [norm_mul]
    exact mul_le_mul (hφB y hy) hderiv (norm_nonneg _) hB
  · exact Filter.Eventually.of_forall (fun y z _ =>
      (sourceKPFiniteIntertwiningKernel_entire K hζ g y z).hasDerivAt.const_mul (φ y))

theorem sourceKPFiniteWindowWeightedIntertwiner_analyticOnNhd
    (g : SourceKPFiniteAdeleProjective K hζ) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φ : 𝔸ᶠ[K] → ℂ) (hφ : Measurable φ) (B : ℝ) (hB : 0 ≤ B)
    (hφB : ∀ y ∈ sourceKPFiniteWindow K S, ‖φ y‖ ≤ B) :
    AnalyticOnNhd ℂ (fun s => sourceKPFiniteWindowIntegral K
      (fun y => φ y * sourceKPFiniteIntertwiningKernel K hζ s g y) S) {s : ℂ | 0 < s.re} := by
  have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ (fun s => sourceKPFiniteWindowIntegral K
      (fun y => φ y * sourceKPFiniteIntertwiningKernel K hζ s g y) S) {s : ℂ | 0 < s.re} :=
    fun _ hs => (sourceKPFiniteWindowWeightedIntertwiner_hasDerivAt K hζ hs g S
      φ hφ B hB hφB).differentiableAt.differentiableWithinAt
  exact fun _ hs => hd.analyticAt (hopen.mem_nhds hs)

theorem sourceKPFiniteWindowIntertwiner_analyticOnNhd
    (g : SourceKPFiniteAdeleProjective K hζ) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    AnalyticOnNhd ℂ (fun s => sourceKPFiniteWindowIntegral K
      (sourceKPFiniteIntertwiningKernel K hζ s g) S) {s : ℂ | 0 < s.re} := by
  simpa only [one_mul] using sourceKPFiniteWindowWeightedIntertwiner_analyticOnNhd K hζ g S
    (fun _ => 1) measurable_const 1 (by norm_num) (fun _ _ => by norm_num)

end
end ArtinMatthews
