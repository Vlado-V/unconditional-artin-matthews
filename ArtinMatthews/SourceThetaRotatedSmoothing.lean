module

public import ArtinMatthews.SourceThetaRotatedSheetBounds
public import ArtinMatthews.SourceThetaAbsoluteSmoothing


set_option backward.privateInPublic true
@[expose] public section

/-! The actual reflected norm-sheet convolution and its derivative
bounds, with the exact signed Mellin moment in each weight estimate. -/
namespace ArtinMatthews.SourceReflection.SourceThetaRotatedTensor

open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory Set
open ArtinMatthews.SourcePhysical
open scoped NumberField Classical ContDiff ArtinMatthews.SourcePhysical
noncomputable section

variable {K : Type} [Field K] [NumberField K]
variable {S : Finset (HeightOneSpectrum (𝓞 K))}
variable {ζ : K} {hζ : IsPrimitiveRoot ζ 12} {v : InfinitePlace K} {δ : ℝ}
variable (d : SourceThetaRotatedTensor K S hζ v δ)
variable (C₀ A₀ : ℝ) (r : ℕ) (τ : ℝ)

def smoothed (j : ℕ) : ℝ → ℂ :=
  sourceThetaGaussianProfile C₀ A₀ r τ (d.sheet j)

def smoothedAbs (j : ℕ) : ℝ → ℝ :=
  sourceThetaGaussianProfileAbs C₀ A₀ r τ
    (sourceThetaSLocalSheetAbs K S hζ v (d.localDeriv j) d.retained)

theorem smoothed_exp (j : ℕ) (t : ℝ) :
    d.smoothed C₀ A₀ r τ j (Real.exp t) =
      sourceThetaGaussianLogSmooth C₀ A₀ r τ (d.logSheet j) t :=
  sourceThetaGaussianProfile_exp C₀ A₀ r τ (d.sheet j) t

theorem smoothedAbs_exp (j : ℕ) (t : ℝ) :
    d.smoothedAbs C₀ A₀ r τ j (Real.exp t) =
      sourceThetaGaussianLogSmoothAbs C₀ A₀ r τ (d.logSheetAbs j) t :=
  sourceThetaGaussianProfileAbs_exp C₀ A₀ r τ
    (sourceThetaSLocalSheetAbs K S hζ v (d.localDeriv j) d.retained) t

theorem smoothedAbs_nonneg (j : ℕ) (t : ℝ) :
    0 ≤ d.smoothedAbs C₀ A₀ r τ j (Real.exp t) := by
  rw [d.smoothedAbs_exp]
  exact integral_nonneg fun _ => mul_nonneg (norm_nonneg _) (d.logSheetAbs_nonneg _ _)

theorem smoothedAbs_weighted (j : ℕ) (σ : ℝ) (hσ : -δ < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t,
      d.smoothedAbs C₀ A₀ r τ j (Real.exp t) ≤
        C * sourceThetaGaussianLogMoment C₀ A₀ r (-τ * σ) * Real.exp (-σ * t) := by
  obtain ⟨C, hC, hb⟩ := d.logSheetAbs_weighted j σ hσ
  refine ⟨C, hC, fun t => ?_⟩
  rw [d.smoothedAbs_exp]
  exact (sourceThetaGaussianLogSmoothAbs_weighted C₀ A₀ r τ σ C
    (d.logSheetAbs j) (d.logSheetAbs_measurable j) (d.logSheetAbs_nonneg j) hb t).2

theorem smoothedAbs_integrable (j : ℕ) (σ : ℝ) (hσ : -δ < σ) {u : ℝ} (hu : 0 < u) :
    IntegrableOn (sourceThetaGaussianProfileAbsIntegrand C₀ A₀ r τ
      (sourceThetaSLocalSheetAbs K S hζ v (d.localDeriv j) d.retained) u) (Ioi 0) := by
  obtain ⟨C, _, hb⟩ := d.logSheetAbs_weighted j σ hσ
  rw [← Real.exp_log hu, sourceThetaGaussianProfileAbs_integrable_iff]
  exact (sourceThetaGaussianLogSmoothAbs_weighted C₀ A₀ r τ σ C (d.logSheetAbs j)
    (d.logSheetAbs_measurable j) (d.logSheetAbs_nonneg j) hb (Real.log u)).1

theorem smoothed_norm_le_abs (hδ : 0 < δ) (j : ℕ) (t : ℝ) :
    ‖d.smoothed C₀ A₀ r τ j (Real.exp t)‖ ≤ d.smoothedAbs C₀ A₀ r τ j (Real.exp t) := by
  obtain ⟨C, _, hb⟩ := d.logSheetAbs_weighted j 0 (neg_lt_zero.mpr hδ)
  have hI := (sourceThetaGaussianLogSmoothAbs_weighted C₀ A₀ r τ 0 C (d.logSheetAbs j)
    (d.logSheetAbs_measurable j) (d.logSheetAbs_nonneg j) hb t).1
  have hc : Continuous (d.logSheet j) :=
    continuous_iff_continuousAt.mpr fun x => (d.logSheet_hasDerivAt hδ j x).continuousAt
  rw [d.smoothed_exp, d.smoothedAbs_exp]
  exact (sourceThetaGaussianLogSmooth_norm_le_abs C₀ A₀ r τ (d.logSheet j) hc.measurable
    (d.logSheetAbs j) (d.logSheet_norm_le_abs j) t hI).2

theorem smoothed_log_hasDerivAt (hδ : 0 < δ) (j : ℕ) (t : ℝ) :
    HasDerivAt (fun x => d.smoothed C₀ A₀ r τ j (Real.exp x))
      (d.smoothed C₀ A₀ r τ (j + 1) (Real.exp t)) t := by
  obtain ⟨C, _, hb⟩ := d.logSheetAbs_weighted j 0 (neg_lt_zero.mpr hδ)
  obtain ⟨C', _, hb'⟩ := d.logSheetAbs_weighted (j + 1) 0 (neg_lt_zero.mpr hδ)
  have hc : Continuous (d.logSheet (j + 1)) :=
    continuous_iff_continuousAt.mpr fun x => (d.logSheet_hasDerivAt hδ (j + 1) x).continuousAt
  simp_rw [d.smoothed_exp]
  exact sourceThetaGaussianLogSmooth_hasDerivAt C₀ A₀ r τ
    (d.logSheet j) (d.logSheet (j + 1)) hc.measurable (d.logSheet_hasDerivAt hδ j)
    C C' (fun x => (d.logSheet_norm_le_abs j x).trans (by simpa using hb x))
    (fun x => (d.logSheet_norm_le_abs (j + 1) x).trans (by simpa using hb' x)) t

theorem smoothed_logSmooth (hδ : 0 < δ) :
    ContDiff ℝ ∞ (fun t => d.smoothed C₀ A₀ r τ 0 (Real.exp t)) :=
  sourceThetaDerivativeFamily_contDiff (fun j t => d.smoothed C₀ A₀ r τ j (Real.exp t))
    (d.smoothed_log_hasDerivAt C₀ A₀ r τ hδ)

theorem smoothed_log_iteratedDeriv (hδ : 0 < δ) (j : ℕ) :
    iteratedDeriv j (fun t => d.smoothed C₀ A₀ r τ 0 (Real.exp t)) =
      fun t => d.smoothed C₀ A₀ r τ j (Real.exp t) :=
  sourceThetaDerivativeFamily_iteratedDeriv (fun j t => d.smoothed C₀ A₀ r τ j (Real.exp t))
    (d.smoothed_log_hasDerivAt C₀ A₀ r τ hδ) j

/-- The signed and absolute derivative estimates needed for Fourier
separation of the actual source profiles. -/
theorem smoothed_logDeriv_twoEnded (hδ : 0 < δ) {α A : ℝ} (hα : α < δ) (hA : -δ < A)
    (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t,
      ‖iteratedFDeriv ℝ j (fun x => d.smoothed C₀ A₀ r τ 0 (Real.exp x)) t‖ +
        d.smoothedAbs C₀ A₀ r τ j (Real.exp t) ≤
      C * min (Real.exp (α * t)) (Real.exp (-A * t)) := by
  obtain ⟨D₁, hD₁, h₁⟩ := d.smoothedAbs_weighted C₀ A₀ r τ j (-α) (by linarith)
  obtain ⟨D₂, hD₂, h₂⟩ := d.smoothedAbs_weighted C₀ A₀ r τ j A hA
  let C₁ := D₁ * sourceThetaGaussianLogMoment C₀ A₀ r (-τ * -α)
  let C₂ := D₂ * sourceThetaGaussianLogMoment C₀ A₀ r (-τ * A)
  let C := max C₁ C₂
  have hC : 0 ≤ C := (mul_nonneg hD₁ (sourceThetaGaussianLogMoment_nonneg C₀ A₀ r _)).trans
    (le_max_left _ _)
  refine ⟨2 * C, by positivity, fun t => ?_⟩
  have hb : d.smoothedAbs C₀ A₀ r τ j (Real.exp t) ≤
      C * min (Real.exp (α * t)) (Real.exp (-A * t)) := by
    rw [mul_min_of_nonneg _ _ hC]
    apply le_min
    · exact (by simpa only [neg_neg, C₁] using h₁ t : _ ≤ C₁ * Real.exp (α * t)).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    · exact (h₂ t).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, d.smoothed_log_iteratedDeriv C₀ A₀ r τ hδ,
    mul_assoc, two_mul]
  exact add_le_add ((d.smoothed_norm_le_abs C₀ A₀ r τ hδ j t).trans hb) hb

end
end ArtinMatthews.SourceReflection.SourceThetaRotatedTensor
