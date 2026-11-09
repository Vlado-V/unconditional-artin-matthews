module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! A genuine Schwartz logarithmic profile for every smooth cutoff supported
away from zero. This supplies Mellin separation through Fourier inversion. -/

namespace ArtinMatthews

open Filter MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff

theorem primeExtraction_logProfile_hasCompactSupport (Φ : ℝ → ℂ) {a b : ℝ}
    (ha : 0 < a) (hsupp : Function.support Φ ⊆ Set.Icc a b) :
    HasCompactSupport (fun u : ℝ => Φ (Real.exp u)) := by
  apply HasCompactSupport.intro' (isCompact_Icc : IsCompact (Set.Icc (Real.log a) (Real.log b)))
    isClosed_Icc
  intro u hu
  by_contra hΦ
  have hh := hsupp hΦ
  apply hu
  refine ⟨?_, ?_⟩
  · simpa only [Real.log_exp] using Real.log_le_log ha hh.1
  · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos u) hh.2

noncomputable def primeExtractionLogProfile (Φ : ℝ → ℂ) {a b : ℝ}
    (ha : 0 < a) (hsupp : Function.support Φ ⊆ Set.Icc a b) (hΦ : ContDiff ℝ ∞ Φ) :
    SchwartzMap ℝ ℂ :=
  (primeExtraction_logProfile_hasCompactSupport Φ ha hsupp).toSchwartzMap
    (hΦ.comp Real.contDiff_exp)

theorem primeExtractionLogProfile_apply (Φ : ℝ → ℂ) {a b : ℝ}
    (ha : 0 < a) (hsupp : Function.support Φ ⊆ Set.Icc a b) (hΦ : ContDiff ℝ ∞ Φ) (u : ℝ) :
    primeExtractionLogProfile Φ ha hsupp hΦ u = Φ (Real.exp u) := rfl

noncomputable def primeExtractionMellinPhase (t y : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * t * Real.log y : ℝ) : ℂ) * Complex.I)

theorem primeExtractionMellinPhase_norm (t y : ℝ) :
    ‖primeExtractionMellinPhase t y‖ = 1 := by
  simp [primeExtractionMellinPhase, Complex.norm_exp]

/-- Exact product separation for positive m,n,x, before restricting frequency. -/
theorem primeExtractionMellinPhase_mul_div (t : ℝ) {m n x : ℝ}
    (hm : 0 < m) (hn : 0 < n) (hx : 0 < x) :
    primeExtractionMellinPhase t (m * n / x) =
      primeExtractionMellinPhase t m * primeExtractionMellinPhase t n *
        primeExtractionMellinPhase (-t) x := by
  unfold primeExtractionMellinPhase
  rw [Real.log_div (mul_ne_zero hm.ne' hn.ne') hx.ne', Real.log_mul hm.ne' hn.ne']
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The actual smooth cutoff equals an absolutely convergent Mellin-type
integral. Both inversion and rapid-decay moments come from its constructed
Schwartz logarithmic profile; neither is an assumed analytic input. -/
theorem primeExtraction_mellin_inversion (Φ : ℝ → ℂ) {a b : ℝ}
    (ha : 0 < a) (hsupp : Function.support Φ ⊆ Set.Icc a b) (hΦ : ContDiff ℝ ∞ Φ)
    {y : ℝ} (hy : 0 < y) :
    (∫ t : ℝ, (𝓕 (primeExtractionLogProfile Φ ha hsupp hΦ)) t *
      primeExtractionMellinPhase t y) = Φ y := by
  let f := primeExtractionLogProfile Φ ha hsupp hΦ
  have hh := congrFun (f.continuous.fourierInv_fourier_eq f.integrable
    (show Integrable (𝓕 (f : ℝ → ℂ)) from (𝓕 f : SchwartzMap ℝ ℂ).integrable)) (Real.log y)
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul] at hh
  calc
    _ = ∫ t : ℝ, Complex.exp (((-2 * Real.pi * t * (-Real.log y) : ℝ) : ℂ) * Complex.I) *
        (𝓕 (f : ℝ → ℂ)) t := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t => by
        dsimp [primeExtractionMellinPhase]
        rw [show ((2 * Real.pi * t * Real.log y : ℝ) : ℂ) * Complex.I =
          ((-2 * Real.pi * t * (-Real.log y) : ℝ) : ℂ) * Complex.I by push_cast; ring]
        rw [congrFun (SchwartzMap.fourier_coe f) t]
        ring)
    _ = f (Real.log y) := by simpa only [smul_eq_mul] using hh
    _ = Φ y := by rw [primeExtractionLogProfile_apply, Real.exp_log hy]

theorem primeExtraction_mellin_moment_integrable (Φ : ℝ → ℂ) {a b : ℝ}
    (ha : 0 < a) (hsupp : Function.support Φ ⊆ Set.Icc a b) (hΦ : ContDiff ℝ ∞ Φ) (k : ℕ) :
    Integrable (fun t : ℝ => |t| ^ k * ‖(𝓕 (primeExtractionLogProfile Φ ha hsupp hΦ)) t‖) := by
  simpa only [Real.norm_eq_abs] using
    (𝓕 (primeExtractionLogProfile Φ ha hsupp hΦ) : SchwartzMap ℝ ℂ).integrable_pow_mul volume k

end ArtinMatthews
