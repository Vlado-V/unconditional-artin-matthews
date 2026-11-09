module

public import ArtinMatthews.SourceKPAdelicStandardConstantTerm
public import ArtinMatthews.SourceKPAdelicIntertwinerHolomorphic
public import ArtinMatthews.SourceAdelicTraceHaar


set_option backward.privateInPublic true
@[expose] public section

/-! The actual constant term and holomorphic intertwining integral for
the prescribed local trace-self-dual Haar product. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance sourceKPTraceConstantTermMeasurable : MeasurableSpace 𝔸[K] := borel 𝔸[K]
local instance sourceKPTraceConstantTermBorel : BorelSpace 𝔸[K] := ⟨rfl⟩

def sourceKPAdelicTraceIntertwiner (s : ℂ) (g : SourceKPAdelicProjective K hζ) : ℂ :=
  sourceKPAdelicIntertwiner K hζ (sourceKPAdelicTraceProduct K) s g

theorem sourceKPAdelicIntertwiningKernel_trace_integrable {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (g : SourceKPAdelicProjective K hζ) :
    Integrable (sourceKPAdelicIntertwiningKernel K hζ s g) (sourceKPAdelicTraceProduct K) := by
  simpa only [sourceKPAdelicTraceProduct_eq_standard_of_primitiveRoot K hζ] using
    sourceKPAdelicIntertwiningKernel_standard_integrable K hζ hs g

theorem sourceKPAdelicTraceIntertwiner_hasDerivAt {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) < 2*s.re+1)
    (g : SourceKPAdelicProjective K hζ) :
    HasDerivAt (fun z : ℂ => sourceKPAdelicTraceIntertwiner K hζ z g)
      (∫ y, deriv (fun z : ℂ => sourceKPAdelicIntertwiningKernel K hζ z g y) s
        ∂sourceKPAdelicTraceProduct K) s := by
  simpa only [sourceKPAdelicTraceIntertwiner,
    sourceKPAdelicTraceProduct_eq_standard_of_primitiveRoot K hζ] using
    sourceKPAdelicIntertwiner_hasDerivAt K hζ (sourceKPAdelicStandardHaar K) hs g

theorem sourceKPAdelicTraceIntertwiner_holomorphic (g : SourceKPAdelicProjective K hζ) :
    DifferentiableOn ℂ (fun s => sourceKPAdelicTraceIntertwiner K hζ s g)
      {s : ℂ | ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) < 2*s.re+1} := by
  simpa only [sourceKPAdelicTraceIntertwiner,
    sourceKPAdelicTraceProduct_eq_standard_of_primitiveRoot K hζ] using
    sourceKPAdelicIntertwiner_holomorphic K hζ (sourceKPAdelicStandardHaar K) g

theorem sourceKPAdelicCompactEisenstein_traceConstantTerm {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (g : SourceKPAdelicProjective K hζ) :
    (∫ y in sourceKPAdelicFundamentalDomain K,
      sourceKPAdelicCompactEisenstein K hζ s (sourceKPAdelicUpperLift K hζ y*g)
        ∂sourceKPAdelicTraceProduct K) =
      sourceKPAdelicCompactScalar K hζ s g + sourceKPAdelicTraceIntertwiner K hζ s g := by
  simpa only [sourceKPAdelicTraceIntertwiner, sourceKPAdelicIntertwiner,
    sourceKPAdelicTraceProduct_eq_standard_of_primitiveRoot K hζ] using
    sourceKPAdelicCompactEisenstein_standardConstantTerm K hζ hs g

end
end ArtinMatthews
