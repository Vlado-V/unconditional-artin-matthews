module

public import ArtinMatthews.SourceCoordinateFiberReduction
public import ArtinMatthews.SourceKPLocalFiberIntegral


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews

open NumberField IsDedekindDomain MeasureTheory StandardAdelic
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance finiteCoordinateLocalCompletionMeasurable (P : HeightOneSpectrum (𝓞 K)) :
    MeasurableSpace (P.adicCompletion K) := borel _
local instance finiteCoordinateLocalCompletionBorel (P : HeightOneSpectrum (𝓞 K)) :
    BorelSpace (P.adicCompletion K) := ⟨rfl⟩

theorem sourceKPFiniteCoordinateFiber_relation
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)
    (s : ℂ) (g : SourceKPFiniteAdeleProjective K hζ)
    (hg : sourceKPAdelicLocalBase K hζ P.val (1, g) = 1)
    (t : sourceKPAdelicCoveringTorus K hζ) (r : 𝔸ᶠ[K]) (hr : r P.val = 0)
    (hP : P.val ∉ traceBadPlaces K) (hs : 0 < s.re) :
    (∫ x : P.val.adicCompletion K,
      sourceKPFiniteCoordinateIntertwiningKernel K hζ s g t.val.2
        (sourceKPFiniteAdditiveSingle K P.val x + r) ∂sourceJacquetHaar K P.val) =
      sourceKPUnramifiedScatteringFactor P.val s *
        ∫ x : P.val.adicCompletion K in (P.val.adicCompletionIntegers K : Set _),
          sourceKPFiniteCoordinateIntertwiningKernel K hζ s g t.val.2
            (sourceKPFiniteAdditiveSingle K P.val x + r) ∂sourceJacquetHaar K P.val := by
  apply sourceKPFiniteCoordinateFiber_relation_of_global K hζ P.val s g t r
    (sourceKPUnramifiedScatteringFactor P.val s)
  simpa only [sourceKPAdelicCoordinateKernel, SourcePhysical.sourceLocalBall_zero] using
    sourceKPLocalFiber_integral_eq_factor_unit_ball K hζ S₀ P s r hr (1, g) hg t hP hs

end
end ArtinMatthews
