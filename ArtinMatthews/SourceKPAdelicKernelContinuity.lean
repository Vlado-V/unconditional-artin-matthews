module

public import ArtinMatthews.SourceKPFiniteUnipotentCompact
public import ArtinMatthews.SourceArchKernelContinuity
public import ArtinMatthews.SourceKPAdelicKernelIntegrable


set_option backward.privateInPublic true
@[expose] public section

/-! Joint adelic continuity and absolute integrability of the actual
global intertwining kernel, followed by the actual constant term. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicCompactScalar_right (s : ℂ) (q : SourceKPAdelicProjective K hζ)
    (k : sourceKPAdelicDeepCompact K hζ) :
    sourceKPAdelicCompactScalar K hζ s (q*k.val) = sourceKPAdelicCompactScalar K hζ s q := by
  have h := congrArg (fun f : SourceKPAdelicPrincipalSeries K hζ s => (f.val q).val 1)
    (sourceKPAdelicCompactSection_right K hζ s k)
  exact h

theorem sourceKPAdelicIntertwiningKernel_finite_uniform (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (t₀ : 𝔸ᶠ[K]) :
    ∀ᶠ t : 𝔸ᶠ[K] in nhds t₀, ∀ u : InfiniteAdeleRing K,
      sourceKPAdelicIntertwiningKernel K hζ s g (u,t) =
        sourceKPAdelicIntertwiningKernel K hζ s g (u,t₀) := by
  have hd : Tendsto (fun t : 𝔸ᶠ[K] => t-t₀) (nhds t₀) (nhds 0) := by
    have hc : Continuous (fun t : 𝔸ᶠ[K] => t-t₀) := continuous_id.sub continuous_const
    simpa only [sub_self] using hc.tendsto t₀
  filter_upwards [hd.eventually (sourceKPAdelicFiniteConjugate_eventually_compact K hζ g)] with t ht
  intro u
  let k : sourceKPAdelicDeepCompact K hζ :=
    ⟨g⁻¹ * sourceKPAdelicUpperLift K hζ (0,t-t₀) * g,ht⟩
  have hadd : ((u,t₀) : 𝔸[K]) + (0,t-t₀) = (u,t) := by
    apply Prod.ext
    · exact add_zero u
    · change t₀+(t-t₀)=t
      abel
  have hn : sourceKPAdelicUpperLift K hζ (u,t₀) *
      sourceKPAdelicUpperLift K hζ (0,t-t₀) = sourceKPAdelicUpperLift K hζ (u,t) :=
    (sourceKPAdelicUpperLift_add K hζ (u,t₀) (0,t-t₀)).symm.trans
      (congrArg (sourceKPAdelicUpperLift K hζ) hadd)
  have he : (sourceKPAdelicProjectiveWeyl K hζ * sourceKPAdelicUpperLift K hζ (u,t₀) * g) * k.val =
      sourceKPAdelicProjectiveWeyl K hζ * sourceKPAdelicUpperLift K hζ (u,t) * g := by
    change (sourceKPAdelicProjectiveWeyl K hζ * sourceKPAdelicUpperLift K hζ (u,t₀) * g) *
      (g⁻¹ * sourceKPAdelicUpperLift K hζ (0,t-t₀) * g) = _
    rw [← hn]
    group
  have h := sourceKPAdelicCompactScalar_right K hζ s
    (sourceKPAdelicProjectiveWeyl K hζ * sourceKPAdelicUpperLift K hζ (u,t₀) * g) k
  rw [he] at h
  exact h

theorem sourceKPAdelicIntertwiningKernel_continuous (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) :
    Continuous (sourceKPAdelicIntertwiningKernel K hζ s g) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  have he : sourceKPAdelicIntertwiningKernel K hζ s g =ᶠ[nhds y]
      (fun z : 𝔸[K] => sourceKPAdelicIntertwiningKernel K hζ s g (z.1,y.2)) := by
    filter_upwards [(continuous_snd.tendsto y).eventually
      (sourceKPAdelicIntertwiningKernel_finite_uniform K hζ s g y.2)] with z hz
    exact hz z.1
  have hc : ContinuousAt (fun z : 𝔸[K] =>
      sourceKPAdelicIntertwiningKernel K hζ s g (z.1,y.2)) y :=
    ((sourceKPAdelicIntertwiningKernel_arch_continuous K hζ s g y.2).comp continuous_fst).continuousAt
  exact hc.congr_of_eventuallyEq he

local instance sourceKPKernelContinuityMeasurable : MeasurableSpace 𝔸[K] := borel 𝔸[K]
local instance sourceKPKernelContinuityBorel : BorelSpace 𝔸[K] := ⟨rfl⟩

theorem sourceKPAdelicIntertwiningKernel_aestronglyMeasurable
    (μ : Measure 𝔸[K]) (s : ℂ) (g : SourceKPAdelicProjective K hζ) :
    AEStronglyMeasurable (sourceKPAdelicIntertwiningKernel K hζ s g) μ :=
  (sourceKPAdelicIntertwiningKernel_continuous K hζ s g).aestronglyMeasurable

theorem sourceKPAdelicIntertwiningKernel_integrable
    (μ : Measure 𝔸[K]) [μ.IsAddHaarMeasure] {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (g : SourceKPAdelicProjective K hζ) :
    Integrable (sourceKPAdelicIntertwiningKernel K hζ s g) μ :=
  sourceKPAdelicIntertwiningKernel_integrable_of_aestronglyMeasurable K hζ μ hs g
    (sourceKPAdelicIntertwiningKernel_aestronglyMeasurable K hζ μ s g)

theorem sourceKPAdelicCompactEisenstein_constantTerm
    (μ : Measure 𝔸[K]) [μ.IsAddHaarMeasure] {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (g : SourceKPAdelicProjective K hζ) :
    (∫ y in sourceKPAdelicFundamentalDomain K,
      sourceKPAdelicCompactEisenstein K hζ s (sourceKPAdelicUpperLift K hζ y*g) ∂μ) =
        μ.real (sourceKPAdelicFundamentalDomain K) • sourceKPAdelicCompactScalar K hζ s g +
          ∫ y, sourceKPAdelicIntertwiningKernel K hζ s g y ∂μ :=
  sourceKPAdelicConstantTerm_integral_of_aestronglyMeasurable K hζ μ hs g
    (sourceKPAdelicIntertwiningKernel_aestronglyMeasurable K hζ μ s g)

end
end ArtinMatthews
