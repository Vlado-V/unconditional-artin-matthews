module

public import Mathlib.Analysis.SpecialFunctions.Bessel
public import ArtinMatthews.ShiftedVoronoiBesselLaplace


set_option backward.privateInPublic true
@[expose] public section

/-!
# Normalization of the weight-one Voronoi Bessel transform

The transform here has exactly the `2πi` scalar and `4π√(xy)` argument of
equation (5.3). Its value on an exponential is computed from the proved
Laplace integral, with all constants retained.
-/

noncomputable section
open MeasureTheory Set Complex

namespace ArtinMatthews

/-- The holomorphic weight-one Bessel transform used in (5.3). -/
def weightOneBesselTransform (H : ℝ → ℂ) (y : ℝ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ) * Complex.I *
    ∫ x in Ioi 0, H x * Complex.besselJ 0 ((4 * Real.pi * Real.sqrt (x * y) : ℝ) : ℂ)

/-- The exact transform of an exponential test function. -/
theorem weightOneBesselTransform_exp (a y : ℝ) (ha : 0 < a) (hy : 0 ≤ y) :
    weightOneBesselTransform (fun x ↦ (Real.exp (-(a * x)) : ℂ)) y =
      ((2 * Real.pi / a : ℝ) : ℂ) * Complex.I *
        (Real.exp (-(4 * Real.pi ^ 2 * y) / a) : ℂ) := by
  have hb : 0 ≤ 4 * Real.pi ^ 2 * y := by positivity
  have he : (∫ x in Ioi 0, (Real.exp (-(a * x)) : ℂ) *
      Complex.besselJ 0 ((4 * Real.pi * Real.sqrt (x * y) : ℝ) : ℂ)) =
      ∫ x in Ioi 0, (Real.exp (-(a * x)) : ℂ) *
        Complex.besselJ 0 (2 * (Real.sqrt ((4 * Real.pi ^ 2 * y) * x) : ℂ)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    congr 2
    rw [show 4 * Real.pi ^ 2 * y * x = (2 * Real.pi) ^ 2 * (x * y) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity : 0 ≤ 2 * Real.pi)]
    push_cast
    ring
  rw [weightOneBesselTransform, he, integral_exp_mul_besselJ_zero_sqrt a _ ha hb]
  push_cast
  ring

end ArtinMatthews
