module

public import ArtinMatthews.SpectralBesselPoisson
public import ArtinMatthews.SpectralGammaVertical


set_option backward.privateInPublic true
@[expose] public section

/-! The actual complex-order Bessel bound used on the exceptional spectral
contour, derived from Poisson's integral and the proved reciprocal-Gamma bound. -/
noncomputable section
namespace ArtinMatthews

open MeasureTheory Set intervalIntegral Complex

/-- A finite nonnegative majorant depending only on the fixed real order. -/
def spectralPoissonMajorant (c : ℝ) : ℝ :=
  ∫ u : ℝ in (-1 : ℝ)..1, ‖(1 - (u : ℂ) ^ 2) ^ ((c : ℂ) - 1 / 2)‖

theorem spectralPoissonMajorant_nonneg (c : ℝ) : 0 ≤ spectralPoissonMajorant c :=
  intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun _ => norm_nonneg _)

/-- The modulus of the oscillating Poisson integrand is independent of the
imaginary part of the order, away from the irrelevant endpoints. -/
theorem spectralPoisson_integral_norm_le (c t x : ℝ) :
    ‖∫ u : ℝ in (-1 : ℝ)..1,
      Complex.exp (Complex.I * (x : ℂ) * u) *
        (1 - (u : ℂ) ^ 2) ^ (((c : ℂ) + 2 * t * Complex.I) - 1 / 2)‖ ≤
      spectralPoissonMajorant c := by
  apply (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (-1 : ℝ) ≤ 1)).trans_eq
  apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num : (-1 : ℝ) ≤ 1)
  intro u hu
  have hb : 0 < 1 - u ^ 2 := by nlinarith [hu.1, hu.2]
  have he : ‖Complex.exp (Complex.I * (x : ℂ) * u)‖ = 1 := by
    rw [Complex.norm_exp]
    norm_num [Complex.mul_re]
  dsimp only
  rw [norm_mul, he, one_mul]
  have hcast : ((1 - u ^ 2 : ℝ) : ℂ) = 1 - (u : ℂ) ^ 2 := by
    push_cast
    rfl
  simp only [← hcast, Complex.norm_cpow_eq_rpow_re_of_pos hb]
  congr 1
  norm_num [Complex.mul_re]

/-- Uniform vertical complex-order bound for the genuine Mathlib Bessel J.
No spectral, Poisson, or Bessel estimate is a hypothesis. -/
theorem spectral_besselJ_vertical_bound (c : ℝ) (hc : 0 ≤ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ t x : ℝ, 0 < x →
      ‖Complex.besselJ ((c : ℂ) + 2 * t * Complex.I) (x : ℂ)‖ ≤
        C * Real.exp (Real.pi * |t|) * x ^ c := by
  obtain ⟨Cg, hCg, hGamma⟩ := spectral_inv_gamma_vertical_bound c hc
  let B := spectralPoissonMajorant c
  have hB : 0 ≤ B := spectralPoissonMajorant_nonneg c
  have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  refine ⟨Cg / Real.sqrt Real.pi * (B + 1), by positivity, ?_⟩
  intro t x hx
  let ν : ℂ := (c : ℂ) + 2 * t * Complex.I
  have hνre : ν.re = c := by simp [ν, Complex.mul_re]
  have hν : -(1 / 2 : ℝ) < ν.re := by rw [hνre]; linarith
  have hcast : ((x / 2 : ℝ) : ℂ) = (x : ℂ) / 2 := by
    push_cast
    rfl
  have hnum : ‖((x : ℂ) / 2) ^ ν‖ = (x / 2) ^ c := by
    rw [← hcast, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), hνre]
  have hnum_le : (x / 2) ^ c ≤ x ^ c :=
    Real.rpow_le_rpow (by positivity) (by linarith) hc
  have harg : ν + 1 / 2 = (((c + 1 / 2 : ℝ) : ℂ) + 2 * t * Complex.I) := by
    dsimp only [ν]
    push_cast
    ring
  have hg : ‖Complex.Gamma (ν + 1 / 2)‖⁻¹ ≤ Cg * Real.exp (Real.pi * |t|) := by
    simpa only [harg, norm_inv] using hGamma t
  have hi := spectralPoisson_integral_norm_le c t x
  change ‖∫ u : ℝ in (-1 : ℝ)..1,
    Complex.exp (Complex.I * (x : ℂ) * u) * (1 - (u : ℂ) ^ 2) ^ (ν - 1 / 2)‖ ≤ B at hi
  rw [spectral_besselJ_poisson ν (x : ℂ) hν, norm_mul, norm_div, norm_mul, hnum,
    Complex.norm_of_nonneg (Real.sqrt_nonneg Real.pi)]
  calc
    _ = ((x / 2) ^ c / Real.sqrt Real.pi) * ‖Complex.Gamma (ν + 1 / 2)‖⁻¹ *
        ‖∫ u : ℝ in (-1 : ℝ)..1,
          Complex.exp (Complex.I * (x : ℂ) * u) * (1 - (u : ℂ) ^ 2) ^ (ν - 1 / 2)‖ := by
      simp only [div_eq_mul_inv, mul_inv]
      ring
    _ ≤ (x ^ c / Real.sqrt Real.pi) * (Cg * Real.exp (Real.pi * |t|)) * (B + 1) := by
      apply mul_le_mul
      · exact mul_le_mul (div_le_div_of_nonneg_right hnum_le hpi.le) hg
          (inv_nonneg.mpr (norm_nonneg _)) (by positivity)
      · exact hi.trans (by linarith)
      · exact norm_nonneg _
      · positivity
    _ = _ := by ring

end ArtinMatthews
