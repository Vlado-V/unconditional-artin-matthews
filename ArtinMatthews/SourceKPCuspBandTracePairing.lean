module

public import ArtinMatthews.SourceKPAutomorphicCuspBandTest
public import ArtinMatthews.SourceKPAutomorphicCompactTruncated
public import ArtinMatthews.SourceKPAdelicTraceConstantTerm


set_option backward.privateInPublic true
@[expose] public section

/-! The literal trace average of the tested, truncated section on a high cusp. -/

namespace ArtinMatthews
open NumberField MeasureTheory
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "πY" => (fun q : SourceKPAdelicProjective K hζ =>
  sourceKPAutomorphicCompactMk K hζ (sourceKPAutomorphicLevelMk K hζ q))

local instance sourceKPCuspBandTraceMeasurable : MeasurableSpace 𝔸[K] := borel 𝔸[K]

/-- Above the cutoff transition, the actual incoming inducing section cancels pointwise. -/
theorem sourceKPAutomorphicCompactTruncatedEisenstein_upper_periodization_of_high {T : ℝ}
    (hT : 1 ≤ T) {s : ℂ} (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (q : SourceKPAdelicProjective K hζ) (hq : 2*T ≤ sourceKPAdelicCoverHeight K hζ q)
    (y : 𝔸[K]) :
    sourceKPAutomorphicCompactTruncatedEisenstein K hζ T s (πY (sourceKPAdelicUpperLift K hζ y*q)) =
      sourceKPAdelicPeriodization K (sourceKPAdelicIntertwiningKernel K hζ s q) y := by
  have hhigh : 1 < sourceKPAdelicCoverHeight K hζ q := by linarith
  rw [sourceKPAutomorphicCompactTruncatedEisenstein_adelic,
    sourceKPAdelicCutoffEisenstein_left_upper_of_high K hζ hT s y q hhigh,
    sourceKPAdelicCutoffEisenstein_eq_of_high K hζ hT s q hq,
    sourceKPAdelicCompactEisenstein_upper_periodization K hζ hs q y, add_sub_cancel_left,
    sourceKPAdelicPeriodization]
  apply tsum_congr
  intro x
  rw [add_comm]

/-- The actual unipotent period of the band pairing uses the prescribed trace Haar. -/
theorem sourceKPCuspBandTracePairing_eq_intertwiner {A B T : ℝ}
    (hA : 1 ≤ A) (hAB : A ≤ B) (hT : 1 ≤ T) (s₀ : ℂ) {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (q : SourceKPAdelicProjective K hζ) (hq : 2*T ≤ sourceKPAdelicCoverHeight K hζ q) :
    (∫ y in sourceKPAdelicFundamentalDomain K,
      star (sourceKPAutomorphicCuspBandTest K hζ A B s₀ (πY (sourceKPAdelicUpperLift K hζ y*q))) *
        sourceKPAutomorphicCompactTruncatedEisenstein K hζ T s
          (πY (sourceKPAdelicUpperLift K hζ y*q)) ∂sourceKPAdelicTraceProduct K) =
      star (sourceKPAutomorphicCuspBandTest K hζ A B s₀ (πY q)) *
        sourceKPAdelicTraceIntertwiner K hζ s q := by
  have hhigh : 1 < sourceKPAdelicCoverHeight K hζ q := by linarith
  simp_rw [sourceKPAutomorphicCuspBandTest_adelic_upper K hζ hA hAB s₀ _ q hhigh,
    sourceKPAutomorphicCompactTruncatedEisenstein_upper_periodization_of_high K hζ hT hs q hq]
  rw [integral_const_mul]
  congr 1
  letI : (sourceKPAdelicTraceProduct K).IsAddHaarMeasure := by
    rw [sourceKPAdelicTraceProduct_eq_standard_of_primitiveRoot K hζ]
    infer_instance
  exact sourceKPAdelicHaarUnfolding K (sourceKPAdelicTraceProduct K)
    (sourceKPAdelicIntertwiningKernel K hζ s q)
    (sourceKPAdelicIntertwiningKernel_trace_integrable K hζ hs q)

end
end ArtinMatthews
