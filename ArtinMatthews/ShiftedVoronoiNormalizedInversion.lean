module

public import ArtinMatthews.ShiftedVoronoiNormalizedMellin
public import OAI.NumberTheory.DirichletL.QuadraticSieve.MainTermDifference
public import Mathlib.Analysis.MellinInversion


set_option backward.privateInPublic true
@[expose] public section

/-!
# Mellin inversion for the normalized radial Fourier transform

The Gamma-pair bound and compact-source Mellin decay are the proved estimates
from OAI's `DirichletL/QuadraticSieve/MainTermDifference.lean`. On a line
`0 < σ < 1`, polynomial Gamma growth is dominated by six powers of source
decay. This proves vertical integrability before applying Mellin inversion.
-/

noncomputable section
open MeasureTheory Set Filter
open OAI.CubicReflectionKernel
open scoped Topology

namespace ArtinMatthews

private theorem gamma_ratio_vertical_bound (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖Complex.Gamma ((σ : ℂ) + t * Complex.I) /
        Complex.Gamma (1 - ((σ : ℂ) + t * Complex.I))‖ ≤
          C * (1 + |t|) ^ 4 := by
  obtain ⟨C, hC, hb⟩ := Gamma_pair_strip_bound 1 (by norm_num) 1
  refine ⟨C / σ, div_pos hC hσ, ?_⟩
  intro t
  have hz : (σ : ℂ) + t * Complex.I ≠ 0 := by
    intro he
    have hh := congrArg Complex.re he
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero, Complex.zero_re] at hh
    linarith
  have hh := hb σ ⟨by linarith, by simpa using hσ1.le⟩ t
  norm_num only [Complex.ofReal_one, Nat.reduceMul, Nat.reduceAdd] at hh
  rw [add_comm (1 : ℂ), Complex.Gamma_add_one _ hz, mul_div_assoc, norm_mul] at hh
  have hnorm : σ ≤ ‖(σ : ℂ) + t * Complex.I‖ := by
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero] using
      Complex.re_le_norm ((σ : ℂ) + t * Complex.I)
  have hh' := (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)).trans hh
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hσ).mpr
  simpa [div_mul_eq_mul_div, mul_comm] using hh'

private theorem normalizedRadialFourier_mellin_vertical_continuous
    (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0 < a)
    (hW : Function.support W ⊆ Icc a b) (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ < 1) :
    Continuous (fun t : ℝ => mellin (normalizedRadialFourier W) ((σ : ℂ) + t * Complex.I)) := by
  have he : (fun t : ℝ => mellin (normalizedRadialFourier W) ((σ : ℂ) + t * Complex.I)) =
      (fun t : ℝ => (Complex.Gamma ((σ : ℂ) + t * Complex.I) /
        Complex.Gamma (1 - ((σ : ℂ) + t * Complex.I))) *
          mellin W (1 - ((σ : ℂ) + t * Complex.I))) := by
    funext t
    exact normalizedRadialFourier_mellin W a b ha hW _
      (by simpa using hσ) (by simpa using hσ1)
  rw [he]
  have hnum : Continuous (fun t : ℝ => Complex.Gamma ((σ : ℂ) + t * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (Gamma_differentiableAt_of_re_pos _ (by simpa using hσ)).continuousAt.comp
      (by fun_prop)
  have hden : Continuous (fun t : ℝ => Complex.Gamma (1 - ((σ : ℂ) + t * Complex.I))) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (Gamma_differentiableAt_of_re_pos _ (by simpa using sub_pos.mpr hσ1)).continuousAt.comp
      (by fun_prop)
  have hne : ∀ t : ℝ, Complex.Gamma (1 - ((σ : ℂ) + t * Complex.I)) ≠ 0 := by
    intro t
    exact Complex.Gamma_ne_zero_of_re_pos (by simpa using sub_pos.mpr hσ1)
  have hsource : Continuous (mellin (W : ℝ → ℂ)) :=
    (compact_source_mellin_differentiable W a b ha hW (W.smooth ⊤)).continuous
  exact (hnum.div hden hne).mul (hsource.comp (by fun_prop))

/-- Two powers of decay on a vertical line, after accounting for the Gamma
quotient's polynomial growth. -/
theorem normalizedRadialFourier_mellin_vertical_bound
    (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0 < a)
    (hW : Function.support W ⊆ Icc a b) (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      (1 + |t|) ^ 2 * ‖mellin (normalizedRadialFourier W) ((σ : ℂ) + t * Complex.I)‖ ≤ C := by
  obtain ⟨Cg, hCg, hg⟩ := gamma_ratio_vertical_bound σ hσ hσ1
  obtain ⟨Cw, hCw, hw⟩ := compact_source_mellin_strip_decay W a b ha hW
    (W.smooth ⊤) (1 - σ) (1 - σ) 6
  refine ⟨Cg * Cw, mul_pos hCg hCw, ?_⟩
  intro t
  have hwb := hw (1 - σ) ⟨le_rfl, le_rfl⟩ (-t)
  rw [abs_neg, show ((1 - σ : ℝ) : ℂ) + (-t : ℝ) * Complex.I =
    1 - ((σ : ℂ) + t * Complex.I) by push_cast; ring] at hwb
  rw [normalizedRadialFourier_mellin W a b ha hW _
    (by simpa using hσ) (by simpa using hσ1), norm_mul]
  calc
    _ ≤ (1 + |t|) ^ 2 * (Cg * (1 + |t|) ^ 4 *
        ‖mellin W (1 - ((σ : ℂ) + t * Complex.I))‖) := by
      gcongr
      exact hg t
    _ = Cg * ((1 + |t|) ^ 6 * ‖mellin W (1 - ((σ : ℂ) + t * Complex.I))‖) := by ring
    _ ≤ Cg * Cw := mul_le_mul_of_nonneg_left hwb hCg.le

/-- The Mellin transform is integrable along each vertical line in the strip. -/
theorem normalizedRadialFourier_mellin_vertical_integrable
    (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0 < a)
    (hW : Function.support W ⊆ Icc a b) (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ < 1) :
    Complex.VerticalIntegrable (mellin (normalizedRadialFourier W)) σ := by
  obtain ⟨C, _, hC⟩ := normalizedRadialFourier_mellin_vertical_bound W a b ha hW σ hσ hσ1
  have hc := normalizedRadialFourier_mellin_vertical_continuous W a b ha hW σ hσ hσ1
  apply (integrable_inv_one_add_sq.const_mul C).mono' hc.aestronglyMeasurable
  exact Eventually.of_forall fun t => by
    simpa only [div_eq_mul_inv] using weighted_two_to_cauchy (norm_nonneg _) t (hC t)

/-- Mellin inversion with vertical integrability derived from the source's
compact support and smoothness. -/
theorem normalizedRadialFourier_mellin_inversion
    (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0 < a)
    (hW : Function.support W ⊆ Icc a b) (σ x : ℝ)
    (hσ : 0 < σ) (hσ1 : σ < 1) (hx : 0 < x) :
    mellinInv σ (mellin (normalizedRadialFourier W)) x = normalizedRadialFourier W x :=
  mellinInv_mellin_eq σ (normalizedRadialFourier W) hx
    (normalizedRadialFourier_mellinConvergent W σ hσ)
    (normalizedRadialFourier_mellin_vertical_integrable W a b ha hW σ hσ hσ1)
    (normalizedRadialFourier_continuous W).continuousAt

/-- The explicit Gamma-quotient inversion formula for the normalized radial
Fourier transform of a compactly supported smooth source. -/
theorem normalizedRadialFourier_gamma_mellin_inversion
    (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0 < a)
    (hW : Function.support W ⊆ Icc a b) (σ x : ℝ)
    (hσ : 0 < σ) (hσ1 : σ < 1) (hx : 0 < x) :
    mellinInv σ (fun s => (Complex.Gamma s / Complex.Gamma (1 - s)) *
      mellin W (1 - s)) x = normalizedRadialFourier W x := by
  rw [← normalizedRadialFourier_mellin_inversion W a b ha hW σ x hσ hσ1 hx]
  unfold mellinInv
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by
    dsimp only
    rw [normalizedRadialFourier_mellin W a b ha hW _
      (by simpa using hσ) (by simpa using hσ1)]

end ArtinMatthews
