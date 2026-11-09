module

public import ArtinMatthews.SourceSLocalRadialHaar
public import ArtinMatthews.SourceLogMellinCoordinate
public import Mathlib.MeasureTheory.Integral.Prod


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory
open scoped NumberField Classical
noncomputable section

variable {K : Type} [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable {v : InfinitePlace K} (hv : IsComplex v)
variable [MeasurableSpace (SWholeUnits K S)] [BorelSpace (SWholeUnits K S)]
variable (ν : Measure (SNormOne K S))
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

/-- The actual norm-one integral at the paper's positive scale. -/
def sourceSLocalSheetProfile (F : SWholeUnits K S → ℂ) (T : ℝ) : ℂ :=
  ∫ n : SNormOne K S, F ((n : SWholeUnits K S) * sLocalPositiveScaling K hζ S T) ∂ν

/-- The norm-weighted integral against the exact radial Haar measure. -/
def sourceSLocalRadialMellin (F : SWholeUnits K S → ℂ) (s : ℂ) : ℂ :=
  ∫ x, F x * (sLocalNorm K S x : ℂ) ^ s ∂sourceSLocalRadialHaar S hv ν

variable [ν.IsHaarMeasure] [SigmaFinite ν]

/-- Bochner disintegration in total logarithmic norm, with the literal all-place section. -/
theorem sourceSLocalRadialHaar_integrable_integral_literal
    (G : SWholeUnits K S → ℂ) (hG : Integrable G (sourceSLocalRadialHaar S hv ν)) :
    Integrable (fun t : ℝ => sourceSLocalSheetProfile S ν hζ G (Real.exp t)) ∧
      (∫ x, G x ∂sourceSLocalRadialHaar S hv ν) =
        ∫ t : ℝ, sourceSLocalSheetProfile S ν hζ G (Real.exp t) := by
  have hm : Measurable (sourceSLocalRadialMulEquiv hv S :
      SNormOne K S × Multiplicative ℝ → SWholeUnits K S) :=
    (sourceSLocalRadialHomeomorph hv S).continuous.measurable
  have hG' : Integrable G (Measure.map (sourceSLocalRadialMulEquiv hv S)
      (ν.prod sourceRealLogHaar)) := hG
  let g := G ∘ (sourceSLocalRadialMulEquiv hv S :
    SNormOne K S × Multiplicative ℝ → SWholeUnits K S)
  have hg : Integrable g (ν.prod sourceRealLogHaar) := hG'.comp_measurable hm
  have hsection (t : ℝ) :
      (∫ n : SNormOne K S, g (n, Multiplicative.ofAdd t) ∂ν) =
        sourceSLocalSheetProfile S ν hζ G (Real.exp t) :=
    sourceSLocal_radial_integral_eq_literal S ν hζ hv G t
  have hi : Integrable (fun t : ℝ => ∫ n : SNormOne K S,
      g (n, Multiplicative.ofAdd t) ∂ν) := hg.integral_prod_right
  refine ⟨hi.congr (Filter.Eventually.of_forall hsection), ?_⟩
  calc
    _ = ∫ p, g p ∂ν.prod sourceRealLogHaar :=
      integral_map hm.aemeasurable hG'.aestronglyMeasurable
    _ = ∫ t : ℝ, ∫ n : SNormOne K S, g (n, Multiplicative.ofAdd t) ∂ν :=
      integral_prod_symm g hg
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall hsection)

omit [MeasurableSpace (SWholeUnits K S)] [BorelSpace (SWholeUnits K S)]
    [ν.IsHaarMeasure] [SigmaFinite ν] in
private theorem sourceSLocalSheetProfile_logWeight
    (F : SWholeUnits K S → ℂ) (s : ℂ) (t : ℝ) :
    sourceSLocalSheetProfile S ν hζ (fun x => F x * (sLocalNorm K S x : ℂ) ^ s)
      (Real.exp t) =
      Complex.exp (s * (t : ℂ)) * sourceSLocalSheetProfile S ν hζ F (Real.exp t) := by
  unfold sourceSLocalSheetProfile
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with n
  rw [sLocalNorm_mul, show sLocalNorm K S n = 1 from n.property, one_mul,
    sLocalPositiveScaling_norm K hζ S (Real.exp_pos t),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero t)),
    ← Complex.ofReal_log (Real.exp_pos t).le, Real.log_exp, mul_comm (t : ℂ) s, mul_comm]

/-- Global weighted integrability gives the Mellin transform of the literal sheet profile. -/
theorem sourceSLocalSheetProfile_hasMellin (F : SWholeUnits K S → ℂ) (s : ℂ)
    (hF : Integrable (fun x => F x * (sLocalNorm K S x : ℂ) ^ s)
      (sourceSLocalRadialHaar S hv ν)) :
    HasMellin (sourceSLocalSheetProfile S ν hζ F) s (sourceSLocalRadialMellin S hv ν F s) := by
  let G := fun x => F x * (sLocalNorm K S x : ℂ) ^ s
  obtain ⟨hG, hEq⟩ := sourceSLocalRadialHaar_integrable_integral_literal S hv ν hζ G hF
  have hw (t : ℝ) := sourceSLocalSheetProfile_logWeight S ν hζ F s t
  refine ⟨(sourceMellinConvergent_iff_log _ _).mpr
    (hG.congr (Filter.Eventually.of_forall hw)), ?_⟩
  rw [sourceMellin_eq_log]
  calc
    _ = ∫ t : ℝ, sourceSLocalSheetProfile S ν hζ G (Real.exp t) :=
      integral_congr_ae (Filter.Eventually.of_forall fun t => (hw t).symm)
    _ = _ := hEq.symm

end
end ArtinMatthews.SourcePhysical
