module

public import ArtinMatthews.SourceThetaSLocalSheet


set_option backward.privateInPublic true
@[expose] public section

/-! Source03 weighted sheet estimates from the chosen local log
derivatives and the retained local weighted integrals. -/
namespace ArtinMatthews.SourceReflection

open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory
open ArtinMatthews.SourcePhysical
open scoped NumberField Classical ContDiff ArtinMatthews.SourcePhysical
noncomputable section

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12) (v : InfinitePlace K)
variable (δ : ℝ)

local notation "μOther" => sourceSLocalOtherUnitMeasure K hζ S v
local notation "N" => sourceSheetOtherNorm S v
local notation "Other" => SNormOneOtherUnits S v

/-- Local data of one genuine split rotated tensor. All differentiations
and norm estimates here concern its local factors. -/
structure SourceThetaRotatedTensor where
  localDeriv : ℕ → Circle → ℝ → ℂ
  retained : Other → ℂ
  local_measurable : ∀ j, Measurable (Function.uncurry (localDeriv j))
  retained_measurable : Measurable retained
  local_hasDerivAt : ∀ j θ t, HasDerivAt (localDeriv j θ) (localDeriv (j + 1) θ t) t
  local_weighted : ∀ j σ, -δ < σ →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ t, ‖localDeriv j θ t‖ ≤ C * Real.exp (-σ * t)
  retained_weighted : ∀ σ, -δ < σ →
    Integrable (fun y => ‖retained y‖ * (N y) ^ σ) μOther

namespace SourceThetaRotatedTensor

variable {K S hζ v δ} (d : SourceThetaRotatedTensor K S hζ v δ)

def sheet (j : ℕ) : ℝ → ℂ :=
  sourceThetaSLocalSheet K S hζ v (d.localDeriv j) d.retained

def logSheet (j : ℕ) (t : ℝ) : ℂ := d.sheet j (Real.exp t)

def logSheetAbs (j : ℕ) (t : ℝ) : ℝ :=
  sourceThetaSLocalSheetAbs K S hζ v (d.localDeriv j) d.retained (Real.exp t)

theorem logSheet_eq (j : ℕ) :
    d.logSheet j = sourceThetaLogSheet μOther N d.retained (d.localDeriv j) :=
  funext (sourceThetaSLocalSheet_exp K S hζ v (d.localDeriv j) d.retained)

theorem logSheetAbs_eq (j : ℕ) :
    d.logSheetAbs j = sourceThetaLogSheetAbs μOther N d.retained (d.localDeriv j) :=
  funext (sourceThetaSLocalSheetAbs_exp K S hζ v (d.localDeriv j) d.retained)

theorem logSheetAbs_measurable (j : ℕ) : Measurable (d.logSheetAbs j) := by
  have : BorelSpace Other := sourceSheetOtherUnits_product_borel S v
  have : SigmaFinite μOther := sourceSLocalOtherUnitMeasure_sigmaFinite K hζ S v
  rw [d.logSheetAbs_eq]
  exact sourceThetaLogSheetAbs_measurable μOther N d.retained
    (measurable_sourceSheetOtherNorm S v) d.retained_measurable (d.local_measurable j)

theorem logSheetAbs_nonneg (j : ℕ) (t : ℝ) : 0 ≤ d.logSheetAbs j t := by
  rw [d.logSheetAbs_eq]
  exact sourceThetaLogSheetAbs_nonneg μOther N d.retained (d.localDeriv j) t

theorem logSheet_norm_le_abs (j : ℕ) (t : ℝ) : ‖d.logSheet j t‖ ≤ d.logSheetAbs j t := by
  rw [d.logSheet_eq, d.logSheetAbs_eq]
  exact sourceThetaLogSheet_norm_le_abs μOther N d.retained (d.localDeriv j) t

theorem logSheetAbs_weighted (j : ℕ) (σ : ℝ) (hσ : -δ < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, d.logSheetAbs j t ≤ C * Real.exp (-σ * t) := by
  have : BorelSpace Other := sourceSheetOtherUnits_product_borel S v
  have : SigmaFinite μOther := sourceSLocalOtherUnitMeasure_sigmaFinite K hζ S v
  obtain ⟨C, hC, hb⟩ := d.local_weighted j σ hσ
  rw [d.logSheetAbs_eq]
  exact (sourceThetaLogSheet_weighted μOther N d.retained (measurable_sourceSheetOtherNorm S v)
    d.retained_measurable (d.local_measurable j) (sourceSheetOtherNorm_pos S v)
    σ C hC hb (d.retained_weighted σ hσ)).2

theorem logSheet_hasDerivAt (hδ : 0 < δ) (j : ℕ) (t : ℝ) :
    HasDerivAt (d.logSheet j) (d.logSheet (j + 1) t) t := by
  have : BorelSpace Other := sourceSheetOtherUnits_product_borel S v
  have : SigmaFinite μOther := sourceSLocalOtherUnitMeasure_sigmaFinite K hζ S v
  have h₀ : -δ < 0 := neg_lt_zero.mpr hδ
  obtain ⟨C, hC, hb⟩ := d.local_weighted j 0 h₀
  obtain ⟨C', _, hb'⟩ := d.local_weighted (j + 1) 0 h₀
  rw [d.logSheet_eq j, d.logSheet_eq (j + 1)]
  exact sourceThetaLogSheet_hasDerivAt μOther N d.retained (measurable_sourceSheetOtherNorm S v)
    d.retained_measurable (d.local_measurable j) (d.local_measurable (j + 1))
    (d.local_hasDerivAt j) (sourceSheetOtherNorm_pos S v) C C' hC
    (fun θ x => by simpa using hb θ x) (fun θ x => by simpa using hb' θ x)
    (by simpa using d.retained_weighted 0 h₀) t

theorem logSheet_contDiff (hδ : 0 < δ) :
    ContDiff ℝ ∞ (d.logSheet 0) :=
  sourceThetaDerivativeFamily_contDiff d.logSheet (d.logSheet_hasDerivAt hδ)

theorem logSheet_iteratedDeriv (hδ : 0 < δ) (j : ℕ) :
    iteratedDeriv j (d.logSheet 0) = d.logSheet j :=
  sourceThetaDerivativeFamily_iteratedDeriv d.logSheet (d.logSheet_hasDerivAt hδ) j

end SourceThetaRotatedTensor
end
end ArtinMatthews.SourceReflection
