module

public import ArtinMatthews.SpectralCuspPoincare


set_option backward.privateInPublic true
@[expose] public section

/-!
Quantitative escape-of-mass control in a two-dimensional hyperbolic cusp.
The mass uses the coordinate density `dx dy / y²`; horizontal Dirichlet energy
uses `dx dy`.  The sole zero-mode assumption is the actual section integral.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff

namespace ArtinMatthews

def cuspHorizontalMass (F : ℝ × ℝ → ℂ) (w y : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..w, ‖F (x, y)‖ ^ 2

def cuspHorizontalEnergy (F : ℝ × ℝ → ℂ) (w y : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..w, ‖deriv (fun t => F (t, y)) x‖ ^ 2

theorem cuspHorizontalMass_nonneg (F : ℝ × ℝ → ℂ) {w : ℝ} (hw : 0 ≤ w)
    (y : ℝ) : 0 ≤ cuspHorizontalMass F w y :=
  intervalIntegral.integral_nonneg hw (fun _ _ => sq_nonneg _)

theorem cuspHorizontalEnergy_nonneg (F : ℝ × ℝ → ℂ) {w : ℝ} (hw : 0 ≤ w)
    (y : ℝ) : 0 ≤ cuspHorizontalEnergy F w y :=
  intervalIntegral.integral_nonneg hw (fun _ _ => sq_nonneg _)

theorem cuspHorizontalMass_stronglyMeasurable {F : ℝ × ℝ → ℂ} (hF : Continuous F)
    {w : ℝ} (hw : 0 ≤ w) : StronglyMeasurable (cuspHorizontalMass F w) := by
  have h := (hF.norm.pow 2).stronglyMeasurable.integral_prod_left'
    (μ := volume.restrict (Ioc 0 w))
  change StronglyMeasurable (fun y => ∫ x in (0 : ℝ)..w, ‖F (x, y)‖ ^ 2)
  simpa only [intervalIntegral.integral_of_le hw, Pi.pow_apply] using h

/-- The actual zero constant term gives the `Y⁻²` factor in the cusp tail.
The implied constant is the square of the cusp width. -/
theorem cusp_horizontal_tail_bound {F : ℝ × ℝ → ℂ} (hF : Continuous F)
    {w Y : ℝ} (hw : 0 < w) (hY : 0 < Y)
    (hsmooth : ∀ y ∈ Ioi Y, ContDiff ℝ ∞ (fun x => F (x, y)))
    (hmean : ∀ y ∈ Ioi Y, (∫ x in (0 : ℝ)..w, F (x, y)) = 0)
    (henergy : IntegrableOn (cuspHorizontalEnergy F w) (Ioi Y)) :
    IntegrableOn (fun y => cuspHorizontalMass F w y / y ^ 2) (Ioi Y) ∧
    (∫ y in Ioi Y, cuspHorizontalMass F w y / y ^ 2) ≤
      (w ^ 2 / Y ^ 2) * ∫ y in Ioi Y, cuspHorizontalEnergy F w y := by
  have hpoint (y : ℝ) (hy : y ∈ Ioi Y) :
      cuspHorizontalMass F w y / y ^ 2 ≤
        (w ^ 2 / Y ^ 2) * cuspHorizontalEnergy F w y := by
    have hypos : 0 < y := hY.trans hy
    have hP := cusp_section_poincare (hsmooth y hy) hw (hmean y hy)
    simp only [sub_zero] at hP
    change cuspHorizontalMass F w y ≤ w ^ 2 * cuspHorizontalEnergy F w y at hP
    calc
      _ ≤ (w ^ 2 * cuspHorizontalEnergy F w y) / y ^ 2 :=
        div_le_div_of_nonneg_right hP (sq_nonneg y)
      _ ≤ (w ^ 2 * cuspHorizontalEnergy F w y) / Y ^ 2 :=
        div_le_div_of_nonneg_left
          (mul_nonneg (sq_nonneg w) (cuspHorizontalEnergy_nonneg F hw.le y))
          (sq_pos_of_pos hY) (sq_le_sq₀ hY.le hypos.le |>.mpr hy.le)
      _ = _ := by ring
  have hm : AEStronglyMeasurable
      (fun y => cuspHorizontalMass F w y / y ^ 2) (volume.restrict (Ioi Y)) :=
    ((cuspHorizontalMass_stronglyMeasurable hF hw.le).measurable.div
      (measurable_id.pow_const 2)).aestronglyMeasurable
  have hdom : ∀ᵐ y ∂volume.restrict (Ioi Y),
      ‖cuspHorizontalMass F w y / y ^ 2‖ ≤
        (w ^ 2 / Y ^ 2) * cuspHorizontalEnergy F w y := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [Real.norm_of_nonneg
      (div_nonneg (cuspHorizontalMass_nonneg F hw.le y) (sq_nonneg y))]
    exact hpoint y hy
  have hi := (henergy.const_mul (w ^ 2 / Y ^ 2)).mono' hm hdom
  refine ⟨hi, ?_⟩
  rw [← integral_const_mul]
  apply integral_mono_ae hi (henergy.const_mul (w ^ 2 / Y ^ 2))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact hpoint y hy

end ArtinMatthews
