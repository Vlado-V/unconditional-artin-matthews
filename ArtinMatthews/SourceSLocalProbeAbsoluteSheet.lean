module

public import ArtinMatthews.SourceSheetAbsoluteProfile
public import ArtinMatthews.SourceSLocalProbeSheetIdentity


set_option backward.privateInPublic true
@[expose] public section

/-! Exact absolute convergence and the norm-decay bound for every physical Fourier sheet. -/

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory
open ArtinMatthews.VaryingKummerAnalytic
open scoped NumberField Classical ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S : Finset (HeightOneSpectrum (𝓞 K))) (v : InfinitePlace K)

local notation "hv" => sourceSLocalComplexPlace K hζ v
local notation "μo" => sourceSLocalOtherUnitMeasure K hζ S v
local notation "ν" => sourceSLocalNormalizedSheetMeasure K hζ S v
local notation "F₀" => sourceSLocalProbeFourierTensor K hζ S v
local notation "G₀" => sourceSLocalProbeRetained K hζ S v
local notation "N" => sourceSheetOtherNorm S v
local notation "P" => sourceSheetProfileIntegrand N sourceProbeArchFourier G₀
local notation "μp" => sourceCircleHaar.prod μo

theorem sourceSLocalProbeSheetScaled_measurable (u : SWholeUnits K S) :
    Measurable (fun x : SNormOne K S => F₀ ((x : SWholeUnits K S) * u)) := by
  have : BorelSpace (SWholeUnits K S) := sourceSWholeUnits_product_borel S v
  have h : Continuous (fun x : SNormOne K S => (x : SWholeUnits K S) * u) :=
    continuous_subtype_val.mul continuous_const
  exact (sourceSLocalProbeFourierTensor_measurable K hζ S v).comp h.measurable

/-- Exact transport of the nonnegative norm integral, at any actual scaling element. -/
theorem sourceSLocalProbeSheetScaled_lintegral_enorm_eq (u : SWholeUnits K S) :
    (∫⁻ x : SNormOne K S, ‖F₀ ((x : SWholeUnits K S) * u)‖ₑ ∂ν) =
      ∫⁻ p : Circle × SNormOneOtherUnits S v,
        ‖P (Real.log (sLocalNorm K S u)) p‖ₑ ∂μp := by
  have : BorelSpace (SNormOneOtherUnits S v) := sourceSheetOtherUnits_product_borel S v
  have : Measure.IsHaarMeasure ν := sourceSLocalNormalizedSheetMeasure_isHaar K hζ S v
  let t := Real.log (sLocalNorm K S u)
  have hN : sLocalNorm K S u = sLocalNorm K S (sourceSLocalRadial hv S t) := by
    rw [sourceSLocalRadial_norm, Real.exp_log (sLocalNorm_pos K S u)]
  calc
    _ = ∫⁻ x : SNormOne K S, ‖F₀ ((x : SWholeUnits K S) * sourceSLocalRadial hv S t)‖ₑ ∂ν :=
      sourceSLocal_sameNorm_lintegral S ν (fun y => ‖F₀ y‖ₑ) u _ hN
    _ = _ := by
      unfold sourceSLocalNormalizedSheetMeasure
      rw [sourceSNormOneSheetMeasure_lintegral]
      apply lintegral_congr
      intro p
      congr 1
      change sourceSLocalChosenTensor S hv sourceProbeArchFourier G₀
        (sourceSLocalRadialSheet S hv p t) = P t p
      rw [sourceSLocalChosenTensor, sourceSLocalRadialSheet_chosen, sourceSLocalRadialSheet_other,
        sourceSheetProfileIntegrand]

private theorem probeProfileIntegrable (t : ℝ) : Integrable (P t) μp := by
  have : BorelSpace (SNormOneOtherUnits S v) := sourceSheetOtherUnits_product_borel S v
  have : SigmaFinite μo := sourceSLocalOtherUnitMeasure_sigmaFinite K hζ S v
  exact (sourceSheetLogProfile_integrable_and_bound μo N (sourceSheetOtherNorm_pos S v)
    (measurable_sourceSheetOtherNorm S v) sourceProbeArchFourier G₀
    (sourceSLocalProbeRetained_measurable K hζ S v) 1 (by norm_num)
    (sourceSLocalProbeRetained_weighted_norm_integrable K hζ S v 1 (by norm_num))).1 t

theorem sourceSLocalProbeSheetScaled_integrable (u : SWholeUnits K S) :
    Integrable (fun x : SNormOne K S => F₀ ((x : SWholeUnits K S) * u)) ν := by
  refine ⟨(sourceSLocalProbeSheetScaled_measurable K hζ S v u).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, sourceSLocalProbeSheetScaled_lintegral_enorm_eq]
  exact (hasFiniteIntegral_iff_enorm.mp
    (probeProfileIntegrable K hζ S v (Real.log (sLocalNorm K S u))).hasFiniteIntegral)

theorem sourceSLocalProbeSheetScaled_integral_norm_eq (u : SWholeUnits K S) :
    (∫ x : SNormOne K S, ‖F₀ ((x : SWholeUnits K S) * u)‖ ∂ν) =
      ∫ p : Circle × SNormOneOtherUnits S v,
        ‖P (Real.log (sLocalNorm K S u)) p‖ ∂μp := by
  rw [integral_norm_eq_lintegral_enorm
      (sourceSLocalProbeSheetScaled_measurable K hζ S v u).aestronglyMeasurable,
    integral_norm_eq_lintegral_enorm
      (probeProfileIntegrable K hζ S v (Real.log (sLocalNorm K S u))).aestronglyMeasurable,
    sourceSLocalProbeSheetScaled_lintegral_enorm_eq]

/-- The absolute physical sheet integral is uniformly bounded at any given S-local norm. -/
theorem sourceSLocalProbeSheetScaled_integral_norm_le (σ : ℝ) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SWholeUnits K S,
      (∫ x : SNormOne K S, ‖F₀ ((x : SWholeUnits K S) * u)‖ ∂ν) ≤
        C * sLocalNorm K S u ^ (-σ) := by
  have : BorelSpace (SNormOneOtherUnits S v) := sourceSheetOtherUnits_product_borel S v
  have : SigmaFinite μo := sourceSLocalOtherUnitMeasure_sigmaFinite K hζ S v
  obtain ⟨C, hC, hbound⟩ := sourceSheetLogProfile_integral_norm_le μo N
    (sourceSheetOtherNorm_pos S v) (measurable_sourceSheetOtherNorm S v) sourceProbeArchFourier G₀
    (sourceSLocalProbeRetained_measurable K hζ S v) σ hσ
    (sourceSLocalProbeRetained_weighted_norm_integrable K hζ S v σ hσ)
  refine ⟨C, hC, fun u => ?_⟩
  rw [sourceSLocalProbeSheetScaled_integral_norm_eq, Real.rpow_def_of_pos (sLocalNorm_pos K S u),
    mul_comm (Real.log (sLocalNorm K S u))]
  exact hbound (Real.log (sLocalNorm K S u))

/-- The positive form of the same estimate can be used before exchanging sums and integrals. -/
theorem sourceSLocalProbeSheetScaled_lintegral_enorm_le (σ : ℝ) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SWholeUnits K S,
      (∫⁻ x : SNormOne K S, ‖F₀ ((x : SWholeUnits K S) * u)‖ₑ ∂ν) ≤
        ENNReal.ofReal (C * sLocalNorm K S u ^ (-σ)) := by
  obtain ⟨C, hC, hbound⟩ := sourceSLocalProbeSheetScaled_integral_norm_le K hζ S v σ hσ
  refine ⟨C, hC, fun u => ?_⟩
  rw [← ofReal_integral_norm_eq_lintegral_enorm
    (sourceSLocalProbeSheetScaled_integrable K hζ S v u)]
  exact ENNReal.ofReal_le_ofReal (hbound u)

theorem sourceSLocalProbeSheet_integrable (T : ℝ) :
    Integrable (fun x : SNormOne K S =>
      F₀ ((x : SWholeUnits K S) * sLocalPositiveScaling K hζ S T)) ν :=
  sourceSLocalProbeSheetScaled_integrable K hζ S v _

/-- The paper's literal all-place section has the same absolute bound. -/
theorem sourceSLocalProbeSheet_integral_norm_le (σ : ℝ) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 < T →
      (∫ x : SNormOne K S, ‖F₀ ((x : SWholeUnits K S) * sLocalPositiveScaling K hζ S T)‖ ∂ν) ≤
        C * T ^ (-σ) := by
  obtain ⟨C, hC, hbound⟩ := sourceSLocalProbeSheetScaled_integral_norm_le K hζ S v σ hσ
  refine ⟨C, hC, fun T hT => ?_⟩
  simpa only [sLocalPositiveScaling_norm K hζ S hT] using hbound (sLocalPositiveScaling K hζ S T)

end
end ArtinMatthews.SourcePhysical
