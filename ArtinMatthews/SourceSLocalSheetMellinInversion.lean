module

public import ArtinMatthews.SourceSLocalSheetMellin


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory
open scoped NumberField Classical Topology
noncomputable section

variable {K : Type} [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable {v : InfinitePlace K} (hv : IsComplex v)
variable [MeasurableSpace (SWholeUnits K S)] [BorelSpace (SWholeUnits K S)]
variable (ν : Measure (SNormOne K S))

private theorem sourceSLocal_weighted_integrable_of_re
    (F : SWholeUnits K S → ℂ) (hF : Measurable F) {σ : ℝ} {s : ℂ} (hs : s.re = σ)
    (hInt : Integrable (fun x => F x * (sLocalNorm K S x : ℂ) ^ (σ : ℂ))
      (sourceSLocalRadialHaar S hv ν)) :
    Integrable (fun x => F x * (sLocalNorm K S x : ℂ) ^ s)
      (sourceSLocalRadialHaar S hv ν) := by
  have hlog : Continuous (fun x => Real.log (sLocalNorm K S x)) :=
    (continuous_sLocalNorm K S).log (fun x => (sLocalNorm_pos K S x).ne')
  have hpow : Measurable (fun x => (sLocalNorm K S x : ℂ) ^ s) := by
    have hEq : (fun x => (sLocalNorm K S x : ℂ) ^ s) =
        fun x => Complex.exp ((Real.log (sLocalNorm K S x) : ℂ) * s) := by
      funext x
      have hx := sLocalNorm_pos K S x
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
        ← Complex.ofReal_log hx.le]
    rw [hEq]
    exact (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp hlog).mul continuous_const)).measurable
  apply hInt.mono (hF.mul hpow).aestronglyMeasurable
  filter_upwards with x
  change ‖F x * (sLocalNorm K S x : ℂ) ^ s‖ ≤
    ‖F x * (sLocalNorm K S x : ℂ) ^ (σ : ℂ)‖
  simp only [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (sLocalNorm_pos K S x),
    hs, Complex.ofReal_re, le_refl]

variable [ν.IsHaarMeasure] [SigmaFinite ν]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

/-- Mellin inversion at a positive scale, using continuity in logarithmic norm. -/
theorem sourceSLocalSheetProfile_mellinInv
    (F : SWholeUnits K S → ℂ) (hF : Measurable F) (σ : ℝ)
    (hInt : Integrable (fun x => F x * (sLocalNorm K S x : ℂ) ^ (σ : ℂ))
      (sourceSLocalRadialHaar S hv ν))
    (hvert : Complex.VerticalIntegrable (sourceSLocalRadialMellin S hv ν F) σ)
    {T : ℝ} (hT : 0 < T)
    (hV : ContinuousAt (fun t : ℝ => sourceSLocalSheetProfile S ν hζ F (Real.exp t))
      (Real.log T)) :
    mellinInv σ (sourceSLocalRadialMellin S hv ν F) T =
      sourceSLocalSheetProfile S ν hζ F T := by
  let V := sourceSLocalSheetProfile S ν hζ F
  have hline (τ : ℝ) : HasMellin V ((σ : ℂ) + (τ : ℂ) * Complex.I)
      (sourceSLocalRadialMellin S hv ν F ((σ : ℂ) + (τ : ℂ) * Complex.I)) :=
    sourceSLocalSheetProfile_hasMellin S hv ν hζ F _
      (sourceSLocal_weighted_integrable_of_re S hv ν F hF (by simp) hInt)
  have hconv : MellinConvergent V (σ : ℂ) :=
    (sourceSLocalSheetProfile_hasMellin S hv ν hζ F (σ : ℂ) hInt).1
  have hvert' : Complex.VerticalIntegrable (mellin V) σ :=
    hvert.congr (Filter.Eventually.of_forall fun τ => (hline τ).2.symm)
  have hcont : ContinuousAt V T := by
    have hEq : (fun x : ℝ => V (Real.exp (Real.log x))) =ᶠ[𝓝 T] V :=
      (eventually_gt_nhds hT).mono fun _ hx => congrArg V (Real.exp_log hx)
    exact (hV.comp (Real.continuousAt_log hT.ne')).congr hEq
  calc
    _ = mellinInv σ (mellin V) T := by
      unfold mellinInv
      congr 1
      apply integral_congr_ae
      filter_upwards with τ
      rw [(hline τ).2]
    _ = _ := mellinInv_mellin_eq σ V hT hconv hvert' hcont

/-- The literal vertical integral uses the factor (1/(2\pi)) and real radial variable. -/
theorem sourceSLocalSheetProfile_eq_verticalIntegral
    (F : SWholeUnits K S → ℂ) (hF : Measurable F) (σ : ℝ)
    (hInt : Integrable (fun x => F x * (sLocalNorm K S x : ℂ) ^ (σ : ℂ))
      (sourceSLocalRadialHaar S hv ν))
    (hvert : Complex.VerticalIntegrable (sourceSLocalRadialMellin S hv ν F) σ)
    {T : ℝ} (hT : 0 < T)
    (hV : ContinuousAt (fun t : ℝ => sourceSLocalSheetProfile S ν hζ F (Real.exp t))
      (Real.log T)) :
    sourceSLocalSheetProfile S ν hζ F T =
      (1 / (2 * Real.pi) : ℝ) • ∫ τ : ℝ,
        (T : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I)) *
          sourceSLocalRadialMellin S hv ν F ((σ : ℂ) + (τ : ℂ) * Complex.I) :=
  (sourceSLocalSheetProfile_mellinInv S hv ν hζ F hF σ hInt hvert hT hV).symm

end
end ArtinMatthews.SourcePhysical
