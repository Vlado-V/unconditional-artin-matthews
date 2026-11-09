module

public import ArtinMatthews.SourceKPAdelicKernelContinuity
public import ArtinMatthews.SourceAdelicStandardHaar


set_option backward.privateInPublic true
@[expose] public section

/-! The actual constant term with the explicit adelic Haar measure
whose rational fundamental domain has mass one. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance sourceKPStandardConstantTermMeasurable : MeasurableSpace 𝔸[K] := borel 𝔸[K]
local instance sourceKPStandardConstantTermBorel : BorelSpace 𝔸[K] := ⟨rfl⟩

theorem sourceKPAdelicIntertwiningKernel_standard_integrable {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (g : SourceKPAdelicProjective K hζ) :
    Integrable (sourceKPAdelicIntertwiningKernel K hζ s g) (sourceKPAdelicStandardHaar K) :=
  sourceKPAdelicIntertwiningKernel_integrable K hζ (sourceKPAdelicStandardHaar K) hs g

theorem sourceKPAdelicCompactEisenstein_standardConstantTerm {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (g : SourceKPAdelicProjective K hζ) :
    (∫ y in sourceKPAdelicFundamentalDomain K,
      sourceKPAdelicCompactEisenstein K hζ s (sourceKPAdelicUpperLift K hζ y*g)
        ∂sourceKPAdelicStandardHaar K) =
      sourceKPAdelicCompactScalar K hζ s g +
        ∫ y, sourceKPAdelicIntertwiningKernel K hζ s g y ∂sourceKPAdelicStandardHaar K := by
  have h := sourceKPAdelicCompactEisenstein_constantTerm K hζ (sourceKPAdelicStandardHaar K) hs g
  simpa only [Measure.real, sourceKPAdelicStandardHaar_fundamentalDomain,
    ENNReal.toReal_one, one_smul] using h

end
end ArtinMatthews
