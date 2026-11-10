module

public import ArtinMatthews.ShiftedVoronoiRadialDuality
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
public import OAI.NumberTheory.DirichletL.Poisson.RadialFourier


set_option backward.privateInPublic true
@[expose] public section

/-!
# The radial Fourier operator in the order-zero Bessel normalization

Rescaling the actual radial Fourier operator removes its Eisenstein lattice
constant. The resulting Laplace law is the law of the kernel `J₀(2√(xy))`.
This file also proves the continuity and integrability needed for uniqueness.
-/

noncomputable section
open MeasureTheory Set Filter
open OAI.EisensteinSchwartzPoisson

namespace ArtinMatthews

/-- The actual radial Fourier transform in the `J₀(2√(xy))` normalization. -/
def normalizedRadialFourier (W : SchwartzMap ℝ ℂ) (y : ℝ) : ℂ :=
  ((1 / radialFourierConstant : ℝ) : ℂ) *
    paperRadialFourier W (y / radialFourierConstant ^ 2)

theorem normalizedRadialFourier_continuous (W : SchwartzMap ℝ ℂ) :
    Continuous (normalizedRadialFourier W) := by
  have hP : Continuous (paperRadialFourier W) := by
    rw [paperRadialFourier_eq_ray]
    exact (paperFourierRayCLM W).continuous.comp Real.continuous_sqrt
  exact continuous_const.mul (hP.comp (continuous_id.div_const _))

theorem normalizedRadialFourier_bounded (W : SchwartzMap ℝ ℂ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : ℝ, ‖normalizedRadialFourier W y‖ ≤ B := by
  refine ⟨(1 / radialFourierConstant) * SchwartzMap.seminorm ℝ 0 0 (paperFourierRayCLM W),
    mul_nonneg (le_of_lt (one_div_pos.mpr radialFourierConstant_pos)) (by positivity), ?_⟩
  intro y
  rw [normalizedRadialFourier, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr radialFourierConstant_pos), paperRadialFourier_eq_ray]
  exact mul_le_mul_of_nonneg_left
    (SchwartzMap.norm_le_seminorm ℝ (paperFourierRayCLM W) _)
    (one_div_pos.mpr radialFourierConstant_pos).le

/-- The normalized transform has an absolutely convergent Laplace integral
at every positive real parameter. -/
theorem normalizedRadialFourier_laplace_integrable (W : SchwartzMap ℝ ℂ)
    (t : ℝ) (ht : 0 < t) :
    IntegrableOn (fun y => normalizedRadialFourier W y *
      Complex.exp (-(t * y : ℝ))) (Ioi 0) := by
  obtain ⟨B, _, hB⟩ := normalizedRadialFourier_bounded W
  have he : IntegrableOn (fun y : ℝ => Complex.exp (-(t * y : ℝ))) (Ioi 0) := by
    simpa only [Complex.neg_re, Complex.ofReal_re, neg_mul, Complex.ofReal_mul,
      Complex.ofReal_neg] using
      integrableOn_exp_mul_complex_Ioi (a := -(t : ℂ)) (by simpa using ht) 0
  exact he.bdd_mul (normalizedRadialFourier_continuous W).aestronglyMeasurable
    (Eventually.of_forall hB)

private theorem radialLaplace_const_mul (f : ℝ → ℂ) (t : ℝ) (c : ℂ) :
    radialLaplace (fun y => c * f y) t = c * radialLaplace f t := by
  simp only [radialLaplace, mul_assoc, integral_const_mul]

private theorem radialLaplace_comp_mul (f : ℝ → ℂ) (t a : ℝ) (ha : 0 < a) :
    radialLaplace (fun y => f (a * y)) t =
      ((1 / a : ℝ) : ℂ) * radialLaplace f (t / a) := by
  unfold radialLaplace
  have he : (fun y : ℝ => f (a * y) * Complex.exp (-(t * y : ℝ))) =
      (fun y : ℝ => (fun u : ℝ => f u * Complex.exp (-((t / a) * u : ℝ))) (a * y)) := by
    funext y
    congr 2
    congr 1
    field_simp
  rw [he]
  simpa only [mul_zero, Complex.real_smul, one_div, Complex.ofReal_inv] using
    integral_comp_mul_left_Ioi
      (fun u : ℝ => f u * Complex.exp (-((t / a) * u : ℝ))) 0 ha

/-- The Laplace law after removal of the lattice normalization. -/
theorem normalizedRadialFourier_laplace (W : SchwartzMap ℝ ℂ)
    (t : ℝ) (ht : 0 < t) :
    radialLaplace (normalizedRadialFourier W) t =
      ((1 / t : ℝ) : ℂ) * radialLaplace W (1 / t) := by
  have hc : radialFourierConstant ≠ 0 := radialFourierConstant_pos.ne'
  have hci : 0 < 1 / radialFourierConstant ^ 2 := by positivity
  change radialLaplace (fun y => ((1 / radialFourierConstant : ℝ) : ℂ) *
    paperRadialFourier W (y / radialFourierConstant ^ 2)) t = _
  rw [radialLaplace_const_mul]
  have he : (fun y => paperRadialFourier W (y / radialFourierConstant ^ 2)) =
      (fun y => paperRadialFourier W ((1 / radialFourierConstant ^ 2) * y)) := by
    funext y
    congr 1
    ring
  rw [he, radialLaplace_comp_mul _ _ _ hci,
    radial_laplace_duality W _ (div_pos ht hci)]
  have harg : radialFourierConstant ^ 2 / (t / (1 / radialFourierConstant ^ 2)) = 1 / t := by
    field_simp
  rw [harg]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hc, Complex.ofReal_ne_zero.mpr ht.ne']

end ArtinMatthews
