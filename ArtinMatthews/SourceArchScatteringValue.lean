module

public import ArtinMatthews.SourceArchScatteringRadial
public import ArtinMatthews.SourceArchScatteringKernel


set_option backward.privateInPublic true
@[expose] public section

/-! The exact archimedean spherical scattering coefficient on its
absolute convergence half-plane. -/
namespace ArtinMatthews.SourceArchJacquet

open MeasureTheory Set
open ArtinMatthews.VaryingKummerAnalytic
noncomputable section

theorem sourceArchShiftedPower_integral {s : ℂ} (hs : 0 < s.re) :
    (∫ t : ℝ in Ioi 0, ((1 + t : ℝ) : ℂ) ^ (-(2 * s + 1))) = (2 * s)⁻¹ := by
  have ha : (-(2 * s + 1)).re < -1 := by
    norm_num [Complex.mul_re]
    linarith
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  calc
    _ = ∫ t : ℝ in Ioi 1, (t : ℂ) ^ (-(2 * s + 1)) :=
      sourceArchIntegral_shift_one (fun u : ℝ => (u : ℂ) ^ (-(2 * s + 1)))
    _ = _ := by
      rw [integral_Ioi_cpow_of_lt ha (by norm_num), Complex.ofReal_one, Complex.one_cpow]
      field_simp
      ring

theorem sourceArchScattering_eq {s : ℂ} (hs : 0 < s.re) :
    sourceArchScattering s = (Real.pi : ℂ) / s := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  unfold sourceArchScattering
  simp_rw [sourceArchSphericalSection_scatteringKernel]
  change (∫ z : ℂ, (fun r : ℝ => ((1 + r ^ 2 : ℝ) : ℂ) ^ (-(2 * s + 1))) ‖z‖
    ∂sourceComplexTraceMeasure) = _
  have hrad := sourceArchTraceIntegral_radial
    (fun r : ℝ => ((1 + r ^ 2 : ℝ) : ℂ) ^ (-(2 * s + 1)))
  rw [hrad]
  change ((4 * Real.pi : ℝ) : ℂ) *
    (∫ r : ℝ in Ioi 0, (r : ℂ) *
      (fun t : ℝ => ((1 + t : ℝ) : ℂ) ^ (-(2 * s + 1))) (r ^ 2)) = _
  have hsq := sourceArchRadialIntegral_square
    (fun t : ℝ => ((1 + t : ℝ) : ℂ) ^ (-(2 * s + 1)))
  rw [hsq, sourceArchShiftedPower_integral hs]
  push_cast
  field_simp
  ring

theorem sourceArchScattering_oneSixth : sourceArchScattering (1 / 6 : ℂ) = 6 * Real.pi := by
  rw [sourceArchScattering_eq (by norm_num)]
  ring

theorem sourceArchScattering_ne_zero {s : ℂ} (hs : 0 < s.re) : sourceArchScattering s ≠ 0 := by
  rw [sourceArchScattering_eq hs]
  exact div_ne_zero (by exact_mod_cast Real.pi_ne_zero) (by intro h; simp [h] at hs)

theorem sourceArchScattering_existingHaar {s : ℂ} (hs : 0 < s.re) :
    (∫ x : ℂ, sourceArchSphericalSection s (sourcePGL2Weyl * sourcePGL2Upper x)
      ∂OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure
        ℂ sourceArchTraceCharacter) = (Real.pi : ℂ) / s := by
  rw [sourceArchTraceCharacter_selfDualMeasure]
  exact sourceArchScattering_eq hs

end
end ArtinMatthews.SourceArchJacquet
