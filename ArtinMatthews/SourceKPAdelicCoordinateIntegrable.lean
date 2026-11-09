module

public import ArtinMatthews.SourceKPAdelicCoordinateKernel
public import ArtinMatthews.SourceKPAdelicKernelContinuity
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Topology.Algebra.Ring.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Every torus coordinate of the spherical-section intertwining
kernel is absolutely integrable in the proved initial half-plane. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance sourceKPCoordinateMeasurable : MeasurableSpace 𝔸[K] := borel 𝔸[K]
local instance sourceKPCoordinateBorel : BorelSpace 𝔸[K] := ⟨rfl⟩

theorem sourceKPAdelicCoordinateKernel_eq_kernel (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (t : sourceKPAdelicCoveringTorus K hζ) (y : 𝔸[K]) :
    sourceKPAdelicCoordinateKernel K hζ s g t y =
      (sourceKPAdelicBorelModularHalf K hζ (sourceKPAdelicBorelTorusInclusion K hζ t))⁻¹ *
        sourceKPAdelicIntertwiningKernel K hζ s ((sourceKPAdelicCoveringTorusWeyl K hζ t).val * g)
          ((sourceKPAdelicTorusIdele K hζ (sourceKPAdelicCoveringTorusWeyl K hζ t) : 𝔸[K]) * y) :=
  sourceKPAdelicCoordinateKernel_eq_scalar K hζ s g t y

theorem sourceKPAdelicCoordinateKernel_continuous (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (t : sourceKPAdelicCoveringTorus K hζ) :
    Continuous (sourceKPAdelicCoordinateKernel K hζ s g t) := by
  change Continuous (fun y : 𝔸[K] => sourceKPAdelicCoordinateKernel K hζ s g t y)
  simp_rw [sourceKPAdelicCoordinateKernel_eq_kernel]
  exact continuous_const.mul
    ((sourceKPAdelicIntertwiningKernel_continuous K hζ s _).comp (continuous_const_mul _))

theorem sourceKPAdelicCoordinateKernel_integrable (μ : Measure 𝔸[K]) [μ.IsAddHaarMeasure]
    {s : ℂ} (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (g : SourceKPAdelicProjective K hζ) (t : sourceKPAdelicCoveringTorus K hζ) :
    Integrable (sourceKPAdelicCoordinateKernel K hζ s g t) μ := by
  let a := sourceKPAdelicTorusIdele K hζ (sourceKPAdelicCoveringTorusWeyl K hζ t)
  let e : 𝔸[K] ≃ₜ+ 𝔸[K] := ContinuousAddEquiv.mulLeft a
  have : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  have hkernel := sourceKPAdelicIntertwiningKernel_integrable K hζ (μ.map e) hs
    ((sourceKPAdelicCoveringTorusWeyl K hζ t).val * g)
  have hcomp := hkernel.comp_measurable e.continuous.measurable
  have hscaled := hcomp.const_mul
    ((sourceKPAdelicBorelModularHalf K hζ (sourceKPAdelicBorelTorusInclusion K hζ t))⁻¹)
  apply hscaled.congr
  exact Filter.Eventually.of_forall (fun y => (sourceKPAdelicCoordinateKernel_eq_kernel K hζ s g t y).symm)

end
end ArtinMatthews
