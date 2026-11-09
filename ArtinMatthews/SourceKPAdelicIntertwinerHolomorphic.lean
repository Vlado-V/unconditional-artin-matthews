module

public import ArtinMatthews.SourceKPAdelicKernelContinuity
public import ArtinMatthews.SourceKPAdelicParameterDerivative
public import Mathlib.Analysis.Calculus.ParametricIntegral


set_option backward.privateInPublic true
@[expose] public section

/-! The actual adelic intertwining integral and its holomorphic
dependence in the initial half-plane. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance sourceKPIntertwinerHolomorphicMeasurable : MeasurableSpace 𝔸[K] := borel 𝔸[K]
local instance sourceKPIntertwinerHolomorphicBorel : BorelSpace 𝔸[K] := ⟨rfl⟩

def sourceKPAdelicIntertwiner (μ : Measure 𝔸[K]) (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) : ℂ :=
  ∫ y, sourceKPAdelicIntertwiningKernel K hζ s g y ∂μ

theorem sourceKPAdelicIntertwiningKernel_deriv_aestronglyMeasurable
    (μ : Measure 𝔸[K]) (s : ℂ) (g : SourceKPAdelicProjective K hζ) :
    AEStronglyMeasurable (fun y : 𝔸[K] =>
      deriv (fun z : ℂ => sourceKPAdelicIntertwiningKernel K hζ z g y) s) μ := by
  apply aestronglyMeasurable_of_tendsto_ae (𝓝[≠] (0 : ℂ))
    (f := fun (u : ℂ) (y : 𝔸[K]) => u⁻¹ • (sourceKPAdelicIntertwiningKernel K hζ (s+u) g y -
      sourceKPAdelicIntertwiningKernel K hζ s g y))
  · intro u
    exact ((sourceKPAdelicIntertwiningKernel_aestronglyMeasurable K hζ μ (s+u) g).sub
      (sourceKPAdelicIntertwiningKernel_aestronglyMeasurable K hζ μ s g)).const_smul (u⁻¹ : ℂ)
  · exact Filter.Eventually.of_forall (fun y =>
      (sourceKPAdelicIntertwiningKernel_entire K hζ g y s).hasDerivAt.tendsto_slope_zero)

theorem sourceKPAdelicIntertwiner_hasDerivAt
    (μ : Measure 𝔸[K]) [μ.IsAddHaarMeasure] {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) < 2*s.re+1)
    (g : SourceKPAdelicProjective K hζ) :
    HasDerivAt (fun z : ℂ => sourceKPAdelicIntertwiner K hζ μ z g)
      (∫ y, deriv (fun z : ℂ => sourceKPAdelicIntertwiningKernel K hζ z g y) s ∂μ) s := by
  let B : ℝ := ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ)
  let δ : ℝ := (2*s.re+1-B)/8
  let a : ℝ := s.re-2*δ
  let b : ℝ := s.re+2*δ
  have hδ : 0 < δ := by dsimp [δ]; change B < 2*s.re+1 at hs; linarith
  have ha : B ≤ 2*(a : ℂ).re+1 := by
    simp only [Complex.ofReal_re]
    dsimp [a,δ]
    change B < 2*s.re+1 at hs
    linarith
  have hb : B ≤ 2*(b : ℂ).re+1 := by
    simp only [Complex.ofReal_re]
    dsimp [b]
    change B < 2*s.re+1 at hs
    linarith
  have hbound : Integrable (fun y : 𝔸[K] => δ⁻¹ *
      (‖sourceKPAdelicIntertwiningKernel K hζ (a : ℂ) g y‖ +
        ‖sourceKPAdelicIntertwiningKernel K hζ (b : ℂ) g y‖)) μ :=
    ((sourceKPAdelicIntertwiningKernel_integrable K hζ μ ha g).norm.add
      (sourceKPAdelicIntertwiningKernel_integrable K hζ μ hb g).norm).const_mul _
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z y => sourceKPAdelicIntertwiningKernel K hζ z g y)
    (F' := fun z y => deriv (fun w : ℂ => sourceKPAdelicIntertwiningKernel K hζ w g y) z)
    (s := Metric.ball s δ) (bound := fun y => δ⁻¹ *
      (‖sourceKPAdelicIntertwiningKernel K hζ (a : ℂ) g y‖ +
        ‖sourceKPAdelicIntertwiningKernel K hζ (b : ℂ) g y‖))
    (Metric.ball_mem_nhds s hδ) _
    (sourceKPAdelicIntertwiningKernel_integrable K hζ μ hs.le g)
    (sourceKPAdelicIntertwiningKernel_deriv_aestronglyMeasurable K hζ μ s g)
    _ hbound _).2
  · exact Filter.Eventually.of_forall (fun z =>
      sourceKPAdelicIntertwiningKernel_aestronglyMeasurable K hζ μ z g)
  · apply Filter.Eventually.of_forall
    intro y z hz
    have hre : |z.re-s.re| < δ := by
      exact lt_of_le_of_lt (by simpa only [Complex.sub_re] using Complex.abs_re_le_norm (z-s))
        (by simpa only [Metric.mem_ball, dist_eq_norm] using hz)
    apply sourceKPAdelicIntertwiningKernel_deriv_bound K hζ a b δ hδ z _ g y
    dsimp [a,b]
    constructor <;> linarith [abs_lt.mp hre]
  · exact Filter.Eventually.of_forall (fun y z _ =>
      (sourceKPAdelicIntertwiningKernel_entire K hζ g y z).hasDerivAt)

theorem sourceKPAdelicIntertwiner_holomorphic
    (μ : Measure 𝔸[K]) [μ.IsAddHaarMeasure] (g : SourceKPAdelicProjective K hζ) :
    DifferentiableOn ℂ (fun s => sourceKPAdelicIntertwiner K hζ μ s g)
      {s : ℂ | ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) < 2*s.re+1} := by
  intro s hs
  exact (sourceKPAdelicIntertwiner_hasDerivAt K hζ μ hs g).differentiableAt.differentiableWithinAt

end
end ArtinMatthews
