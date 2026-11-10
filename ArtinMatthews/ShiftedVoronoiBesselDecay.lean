module

public import ArtinMatthews.ShiftedVoronoiBesselTransform
public import OAI.NumberTheory.DirichletL.Fourier.PositiveLogProfiles
public import OAI.NumberTheory.DirichletL.GaussSum.SexticRadialPoisson
public import ArtinMatthews.ShiftedVoronoiBesselIdentification
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
public import OAI.NumberTheory.DirichletL.Poisson.RadialFourier


set_option backward.privateInPublic true
@[expose] public section

/-!
# Rapid decay of the actual weight-one Bessel transform

The identification with Schwartz Fourier transform proves arbitrary polynomial
decay for compact smooth sources. All normalization constants agree with (5.3).
-/

noncomputable section
open MeasureTheory Set Complex OAI
open OAI.EisensteinSchwartzPoisson

namespace ArtinMatthews

theorem weightOneBesselTransform_eq_radialFourier
    (W : SchwartzMap ℝ ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hWs : Function.support W ⊆ Icc 0 B) (y : ℝ) (hy : 0 < y) :
    weightOneBesselTransform W y =
      (Real.sqrt 3 : ℂ) * Complex.I * paperRadialFourier W (3 * y) := by
  have hk : weightOneBesselTransform W y =
      ((2 * Real.pi : ℝ) : ℂ) * Complex.I *
        besselZeroTransform W (4 * Real.pi ^ 2 * y) := by
    unfold weightOneBesselTransform besselZeroTransform
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    congr 2
    rw [show x * (4 * Real.pi ^ 2 * y) = (2 * Real.pi) ^ 2 * (x * y) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity : 0 ≤ 2 * Real.pi)]
    push_cast
    ring
  rw [hk, besselZeroTransform_eq_normalizedRadialFourier W B hB hWs (by
    change 0 < 4 * Real.pi ^ 2 * y
    positivity), normalizedRadialFourier]
  have harg : 4 * Real.pi ^ 2 * y / radialFourierConstant ^ 2 = 3 * y := by
    rw [radialFourierConstant_sq]
    field_simp
  rw [harg]
  unfold radialFourierConstant
  push_cast
  field_simp

theorem weightOneBesselTransform_rapid_decay
    (W : SchwartzMap ℝ ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hWs : Function.support W ⊆ Icc 0 B) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 0 < y →
      (1 + y) ^ A * ‖weightOneBesselTransform W y‖ ≤ C := by
  obtain ⟨C, hC, hc⟩ := paperRadialFourier_euler_bound W A 0
  refine ⟨Real.sqrt 3 * C, by positivity, ?_⟩
  intro y hy
  have hb := hc 0 (by rfl) (3 * y) (by positivity)
  simp only [LocalLogFourier.eulerDeriv, iteratedDeriv_zero, Real.exp_zero, mul_one] at hb
  rw [weightOneBesselTransform_eq_radialFourier W B hB hWs y hy,
    norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 3)]
  calc
    (1 + y) ^ A * (Real.sqrt 3 * ‖paperRadialFourier W (3 * y)‖) =
        Real.sqrt 3 * ((1 + y) ^ A * ‖paperRadialFourier W (3 * y)‖) := by ring
    _ ≤ Real.sqrt 3 * ((1 + 3 * y) ^ A * ‖paperRadialFourier W (3 * y)‖) := by
      gcongr
      linarith
    _ ≤ Real.sqrt 3 * C := mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg 3)

end ArtinMatthews
