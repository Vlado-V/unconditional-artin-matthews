module

public import ArtinMatthews.SpectralBesselMellinEvaluation


set_option backward.privateInPublic true
@[expose] public section

/-! The literal complex-place positive theta profile in source 03. The
square-root substitution retains its factor two, and the Mellin integral
converges on the actual half-plane Re(s)>−5/6. -/
namespace ArtinMatthews.SourceReflection

open MeasureTheory Set Complex OAI.CubicEisenstein
noncomputable section

/-- The radial factor at a complex place in the positive norm sheet. -/
def sourceThetaBesselProfile (c t : ℝ) : ℂ :=
  (t : ℂ) * schlafliBesselK (1 / 3 : ℂ) (c * Real.sqrt t)

private theorem sourceThetaBesselProfile_as_cpow (c : ℝ) :
    sourceThetaBesselProfile c = fun t : ℝ => (t : ℂ) ^ (1 : ℂ) •
      schlafliBesselK (1 / 3 : ℂ) (c * t ^ (1 / 2 : ℝ)) := by
  funext t
  simp only [sourceThetaBesselProfile, Complex.cpow_one, smul_eq_mul, Real.sqrt_eq_rpow]

private theorem sourceThetaBesselMellin_order (s : ℂ) (hs : -(5 / 6 : ℝ) < s.re) :
    |(1 / 3 : ℂ).re| < (2 * s + 2 : ℂ).re := by
  norm_num [Complex.div_ofNat_re, Complex.add_re, Complex.mul_re]
  linarith

private theorem sourceThetaBesselMellin_scale (s : ℂ) :
    (s + 1) / ((1 / 2 : ℝ) : ℂ) = 2 * s + 2 := by
  push_cast
  ring

theorem sourceThetaBesselProfile_mellinConvergent {c : ℝ} (hc : 0 < c) (s : ℂ)
    (hs : -(5 / 6 : ℝ) < s.re) : MellinConvergent (sourceThetaBesselProfile c) s := by
  rw [sourceThetaBesselProfile_as_cpow, MellinConvergent.cpow_smul,
    MellinConvergent.comp_rpow (f := fun t : ℝ => schlafliBesselK (1 / 3) (c * t))
      (by norm_num : (1 / 2 : ℝ) ≠ 0), sourceThetaBesselMellin_scale]
  simpa only [MellinConvergent, smul_eq_mul] using
    schlafliBesselK_scaled_mellin_integrable (1 / 3) (2 * s + 2)
      (sourceThetaBesselMellin_order s hs) hc

/-- Exact local source03 Mellin integral of t K_(1/3)(c sqrt(t)). -/
theorem sourceThetaBesselProfile_mellin {c : ℝ} (hc : 0 < c) (s : ℂ)
    (hs : -(5 / 6 : ℝ) < s.re) :
    mellin (sourceThetaBesselProfile c) s = (2 : ℂ) ^ (2 * s + 1) * (c : ℂ) ^ (-2 * s - 2) *
      Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6) := by
  rw [sourceThetaBesselProfile_as_cpow, mellin_cpow_smul,
    mellin_comp_rpow (fun t : ℝ => schlafliBesselK (1 / 3) (c * t)) (s + 1) (1 / 2),
    sourceThetaBesselMellin_scale]
  have hm := schlafliBesselK_scaled_mellin (1 / 3) (2 * s + 2)
    (sourceThetaBesselMellin_order s hs) hc
  change mellin (fun t : ℝ => schlafliBesselK (1 / 3) (c * t)) (2 * s + 2) = _ at hm
  rw [hm, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), Complex.real_smul]
  norm_num only [one_div, inv_inv, Complex.ofReal_ofNat]
  rw [show -(2 * s + 2) = -2 * s - 2 by ring,
    show (2 * s + 2 - 2 : ℂ) = 2 * s by ring,
    show (2 * s + 2 - 1 / 3 : ℂ) / 2 = s + 5 / 6 by ring,
    show (2 * s + 2 + 1 / 3 : ℂ) / 2 = s + 7 / 6 by ring]
  have hp : (2 : ℂ) * (2 : ℂ) ^ (2 * s) = (2 : ℂ) ^ (2 * s + 1) := by
    rw [Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0), Complex.cpow_one, mul_comm]
  rw [← hp]
  ring

theorem sourceThetaBesselProfile_hasMellin {c : ℝ} (hc : 0 < c) (s : ℂ)
    (hs : -(5 / 6 : ℝ) < s.re) :
    HasMellin (sourceThetaBesselProfile c) s ((2 : ℂ) ^ (2 * s + 1) * (c : ℂ) ^ (-2 * s - 2) *
      Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) :=
  ⟨sourceThetaBesselProfile_mellinConvergent hc s hs, sourceThetaBesselProfile_mellin hc s hs⟩

end
end ArtinMatthews.SourceReflection
