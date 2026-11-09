module

public import ArtinMatthews.SourceSLocalRadialInvariance
public import ArtinMatthews.SourceRealLogHaar


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory
open scoped NumberField Classical ENNReal
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable {v : InfinitePlace K} (hv : IsComplex v)
variable [MeasurableSpace (SWholeUnits K S)] [BorelSpace (SWholeUnits K S)]

/-- Haar on the literal S-local unit group obtained from a sheet Haar and log Lebesgue measure.
The later comparison with the product of exact local Haar measures fixes the sheet Haar. -/
def sourceSLocalRadialHaar (ν : Measure (SNormOne K S)) : Measure (SWholeUnits K S) :=
  Measure.map (sourceSLocalRadialMulEquiv hv S) (ν.prod sourceRealLogHaar)

theorem sourceSLocalRadialHaar_isHaar (ν : Measure (SNormOne K S))
    [ν.IsHaarMeasure] [SigmaFinite ν] : (sourceSLocalRadialHaar S hv ν).IsHaarMeasure :=
  (sourceSLocalRadialMulEquiv hv S).isHaarMeasure_map (ν.prod sourceRealLogHaar)
    (sourceSLocalRadialHomeomorph hv S).continuous (sourceSLocalRadialHomeomorph hv S).symm.continuous

theorem sourceSLocalRadialHaar_lintegral (ν : Measure (SNormOne K S)) [SigmaFinite ν]
    (F : SWholeUnits K S → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, F x ∂sourceSLocalRadialHaar S hv ν) =
      ∫⁻ t : ℝ, ∫⁻ n : SNormOne K S, F ((n : SWholeUnits K S) * sourceSLocalRadial hv S t) ∂ν := by
  have hm : Measurable (sourceSLocalRadialMulEquiv hv S :
      SNormOne K S × Multiplicative ℝ → SWholeUnits K S) :=
    (sourceSLocalRadialHomeomorph hv S).continuous.measurable
  rw [sourceSLocalRadialHaar, lintegral_map hF hm]
  let g : SNormOne K S × Multiplicative ℝ → ℝ≥0∞ :=
    fun p => F (sourceSLocalRadialMulEquiv hv S p)
  exact lintegral_prod_symm g (hF.comp hm).aemeasurable

theorem sourceSLocalRadialHaar_lintegral_literal (ν : Measure (SNormOne K S))
    [ν.IsHaarMeasure] [SigmaFinite ν] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (F : SWholeUnits K S → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, F x ∂sourceSLocalRadialHaar S hv ν) =
      ∫⁻ t : ℝ, ∫⁻ n : SNormOne K S, F ((n : SWholeUnits K S) *
        sLocalPositiveScaling K hζ S (Real.exp t)) ∂ν := by
  rw [sourceSLocalRadialHaar_lintegral S hv ν F hF]
  apply lintegral_congr
  intro t
  apply sourceSLocal_sameNorm_lintegral S ν F
  rw [sourceSLocalRadial_norm, sLocalPositiveScaling_norm K hζ S (Real.exp_pos _)]

end
end ArtinMatthews.SourcePhysical
