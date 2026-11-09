module

public import ArtinMatthews.SourceEisensteinCuspMean
public import ArtinMatthews.SourceEisensteinUpperContinuity
public import ArtinMatthews.SourceKPCuspSobolev


set_option backward.privateInPublic true
@[expose] public section

/-! The actual cusp remainder is a continuous zero-mean function, hence an
actual trace-Haar L2 vector on the genuine principal cusp torus. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (g : SourceKPAdelicProjective K hζ)
local notation "D" => sourceKPCuspChosenPeriod K hζ g
local notation "Q" => SourceKPCuspPrincipalQuotient K D
local instance sourceEisensteinCuspContinuousMeasurable : MeasurableSpace Q := borel Q
local instance sourceEisensteinCuspContinuousBorel : BorelSpace Q := ⟨rfl⟩

theorem sourceKPCuspNonconstantEisenstein_continuous {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1) :
    Continuous (sourceKPCuspNonconstantEisenstein K hζ g s) := by
  apply (QuotientAddGroup.isQuotientMap_mk (sourceKPCuspPrincipalPeriods K D)).continuous_iff.mpr
  simpa only [Function.comp_def, sourceKPCuspNonconstantEisenstein_mk] using
    sourceKPAdelicNonconstantEisenstein_upper_continuous K hζ hs g

def sourceKPCuspNonconstantEisensteinContinuous {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1) : C(Q,ℂ) :=
  ⟨sourceKPCuspNonconstantEisenstein K hζ g s,
    sourceKPCuspNonconstantEisenstein_continuous K hζ g hs⟩

theorem sourceKPCuspNonconstantEisenstein_actual_mean_zero {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1) :
    (∫ q, sourceKPCuspNonconstantEisenstein K hζ g s q ∂sourceKPCuspTraceHaar K D) = 0 :=
  sourceKPCuspNonconstantEisenstein_mean_zero K hζ g hs
    (sourceKPCuspNonconstantEisenstein_continuous K hζ g hs).aestronglyMeasurable

def sourceKPCuspNonconstantEisensteinL2 {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1) : SourceKPCuspL2 K D :=
  sourceKPCuspContinuousL2 K D hζ (sourceKPCuspChosenPeriod_ne_zero K hζ g)
    (sourceKPCuspNonconstantEisensteinContinuous K hζ g hs)

theorem sourceKPCuspNonconstantEisensteinL2_coe {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1) :
    sourceKPCuspNonconstantEisensteinL2 K hζ g hs =ᵐ[sourceKPCuspTraceHaar K D]
      sourceKPCuspNonconstantEisenstein K hζ g s :=
  sourceKPCuspContinuousL2_coe K D hζ (sourceKPCuspChosenPeriod_ne_zero K hζ g)
    (sourceKPCuspNonconstantEisensteinContinuous K hζ g hs)

theorem sourceKPCuspNonconstantEisensteinL2_mean_zero {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1) :
    (∫ q, sourceKPCuspNonconstantEisensteinL2 K hζ g hs q ∂sourceKPCuspTraceHaar K D) = 0 :=
  (integral_congr_ae (sourceKPCuspNonconstantEisensteinL2_coe K hζ g hs)).trans
    (sourceKPCuspNonconstantEisenstein_actual_mean_zero K hζ g hs)

end
end ArtinMatthews
