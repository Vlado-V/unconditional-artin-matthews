module

public import ArtinMatthews.SourceKPCuspBandTracePairing


set_option backward.privateInPublic true
@[expose] public section

/-! A weight constant along the actual unipotent fibre pulls out of its trace average. -/

namespace ArtinMatthews
open NumberField MeasureTheory
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "πY" => (fun q : SourceKPAdelicProjective K hζ =>
  sourceKPAutomorphicCompactMk K hζ (sourceKPAutomorphicLevelMk K hζ q))

local instance sourceKPCuspBandWeightTraceMeasurable : MeasurableSpace 𝔸[K] := borel 𝔸[K]

theorem sourceKPCuspBandTraceWeight_eq_intertwiner
    (W : SourceKPAutomorphicCompactLevel K hζ → ℂ) {T : ℝ} (hT : 1 ≤ T) {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (q : SourceKPAdelicProjective K hζ) (hq : 2*T ≤ sourceKPAdelicCoverHeight K hζ q)
    (hW : ∀ y : 𝔸[K], W (πY (sourceKPAdelicUpperLift K hζ y*q)) = W (πY q)) :
    (∫ y in sourceKPAdelicFundamentalDomain K,
      star (W (πY (sourceKPAdelicUpperLift K hζ y*q))) *
        sourceKPAutomorphicCompactTruncatedEisenstein K hζ T s
          (πY (sourceKPAdelicUpperLift K hζ y*q)) ∂sourceKPAdelicTraceProduct K) =
      star (W (πY q)) * sourceKPAdelicTraceIntertwiner K hζ s q := by
  simp_rw [hW, sourceKPAutomorphicCompactTruncatedEisenstein_upper_periodization_of_high K hζ hT hs q hq]
  rw [integral_const_mul]
  congr 1
  haveI : (sourceKPAdelicTraceProduct K).IsAddHaarMeasure := by
    rw [sourceKPAdelicTraceProduct_eq_standard_of_primitiveRoot K hζ]
    infer_instance
  exact sourceKPAdelicHaarUnfolding K (sourceKPAdelicTraceProduct K)
    (sourceKPAdelicIntertwiningKernel K hζ s q)
    (sourceKPAdelicIntertwiningKernel_trace_integrable K hζ hs q)

end
end ArtinMatthews
