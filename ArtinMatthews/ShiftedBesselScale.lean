module

public import ArtinMatthews.ShiftedVoronoiBesselDecay
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper


set_option backward.privateInPublic true
@[expose] public section

/-!
# Exact Bessel scaling and uniform derivative control

The higher derivative estimate is transported from the existing OAI radial
Fourier source-seminorm theorem. Only the proved identification with the actual
J0 kernel and an exact change of variables are needed here.
-/

noncomputable section
open MeasureTheory Set Complex OAI
open OAI.EisensteinSchwartzPoisson
open scoped ContDiff

namespace ArtinMatthews

/-- The exact dilation law of the paper's 2πi J0 transform. -/
theorem weightOneBesselTransform_dilate (W : ℝ → ℂ) (K y : ℝ) (hK : 0 < K) :
    weightOneBesselTransform (fun x ↦ W (x / K)) y =
      (K : ℂ) * weightOneBesselTransform W (K * y) := by
  let g (x : ℝ) := W (x / K) * Complex.besselJ 0 ((4 * Real.pi * Real.sqrt (x * y) : ℝ) : ℂ)
  have hi := integral_comp_mul_left_Ioi' g 0 hK
  simp only [mul_zero] at hi
  have he : (fun x : ℝ ↦ g (K*x)) =
      fun x : ℝ ↦ W x * Complex.besselJ 0 ((4 * Real.pi * Real.sqrt (x * (K*y)) : ℝ) : ℂ) := by
    funext x
    dsimp [g]
    rw [mul_div_cancel_left₀ x hK.ne', show K*x*y = x*(K*y) by ring]
  rw [he] at hi
  unfold weightOneBesselTransform
  change _ * _ * (∫ x in Ioi 0, g x) = _
  rw [← hi, Complex.real_smul]
  ring

/-- Smoothness along every positive logarithmic ray is inherited from the
actual Schwartz radial Fourier transform. -/
theorem weightOneBesselTransform_log_smooth (W : SchwartzMap ℝ ℂ) (B : ℝ)
    (hB : 0 ≤ B) (hWs : Function.support W ⊆ Icc 0 B) (y : ℝ) (hy : 0 < y) :
    ContDiff ℝ ∞ (fun t : ℝ ↦ weightOneBesselTransform W (y * Real.exp t)) := by
  have hsm : ContDiff ℝ ∞ (fun t : ℝ ↦ paperRadialFourier W ((3*y) * Real.exp t)) :=
    (paperRadialFourier_contDiffOn W).comp_contDiff
    (show ContDiff ℝ ∞ (fun t : ℝ ↦ (3*y) * Real.exp t) by fun_prop)
    (fun t ↦ show (3*y) * Real.exp t ∈ Ioi 0 by exact mul_pos (mul_pos (by norm_num) hy) (Real.exp_pos t))
  convert (contDiff_const.mul hsm : ContDiff ℝ ∞
    (fun t : ℝ ↦ ((Real.sqrt 3 : ℂ) * Complex.I) * paperRadialFourier W ((3*y) * Real.exp t))) using 1
  funext t
  rw [weightOneBesselTransform_eq_radialFourier W B hB hWs _ (by positivity)]
  congr 2
  ring

/-- Euler derivatives transfer with no derivative loss from the existing
radial Fourier theorem to the exact J0 normalization. -/
theorem weightOneBesselTransform_euler_eq (W : SchwartzMap ℝ ℂ) (B : ℝ)
    (hB : 0 ≤ B) (hWs : Function.support W ⊆ Icc 0 B) (j : ℕ) (y : ℝ) (hy : 0 < y) :
    LocalLogFourier.eulerDeriv (weightOneBesselTransform W) j y =
      (Real.sqrt 3 : ℂ) * Complex.I *
        LocalLogFourier.eulerDeriv (paperRadialFourier W) j (3*y) := by
  have he : (fun t : ℝ ↦ weightOneBesselTransform W (y * Real.exp t)) =
      fun t : ℝ ↦ ((Real.sqrt 3 : ℂ) * Complex.I) * paperRadialFourier W ((3*y) * Real.exp t) := by
    funext t
    rw [weightOneBesselTransform_eq_radialFourier W B hB hWs _ (by positivity)]
    congr 2
    ring
  have hsm : ContDiff ℝ ∞ (fun t : ℝ ↦ paperRadialFourier W ((3*y) * Real.exp t)) :=
    (paperRadialFourier_contDiffOn W).comp_contDiff
    (show ContDiff ℝ ∞ (fun t : ℝ ↦ (3*y) * Real.exp t) by fun_prop)
    (fun t ↦ show (3*y) * Real.exp t ∈ Ioi 0 by exact mul_pos (mul_pos (by norm_num) hy) (Real.exp_pos t))
  unfold LocalLogFourier.eulerDeriv
  rw [he]
  exact iteratedDeriv_const_mul _ (hsm.of_le (by simp)).contDiffAt

/-- Every fixed number of Euler derivatives satisfies arbitrary polynomial
decay, uniformly in the source through finitely many Schwartz seminorms. -/
theorem weightOneBesselTransform_euler_source_bound (A J : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : SchwartzMap ℝ ℂ) (B : ℝ), 0 ≤ B → Function.support W ⊆ Icc 0 B →
        ∀ (j : ℕ), j ≤ J → ∀ (y : ℝ), 0 < y →
          (1+y)^A * ‖LocalLogFourier.eulerDeriv (weightOneBesselTransform W) j y‖ ≤
            C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  obtain ⟨s,C,hC,hb⟩ := paperRadialFourier_euler_source_weighted_bound A J
  refine ⟨s,Real.sqrt 3*C,by positivity,?_⟩
  intro W B hB hWs j hj y hy
  have hx := hb W j hj (3*y) (by positivity)
  rw [weightOneBesselTransform_euler_eq W B hB hWs j y hy,
    norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 3)]
  calc
    _ = Real.sqrt 3*((1+y)^A * ‖LocalLogFourier.eulerDeriv (paperRadialFourier W) j (3*y)‖) := by ring
    _ ≤ Real.sqrt 3*((1+3*y)^A * ‖LocalLogFourier.eulerDeriv (paperRadialFourier W) j (3*y)‖) := by
      gcongr
      linarith
    _ ≤ Real.sqrt 3*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) :=
      mul_le_mul_of_nonneg_left hx (Real.sqrt_nonneg 3)
    _ = _ := by ring

/-- Exact Euler derivative scaling; the derivative is with respect to log y. -/
theorem weightOneBesselTransform_dilate_euler (W : SchwartzMap ℝ ℂ) (B : ℝ)
    (hB : 0 ≤ B) (hWs : Function.support W ⊆ Icc 0 B)
    (K y : ℝ) (hK : 0 < K) (hy : 0 < y) (j : ℕ) :
    LocalLogFourier.eulerDeriv (weightOneBesselTransform (fun x ↦ W (x/K))) j y =
      (K : ℂ) * LocalLogFourier.eulerDeriv (weightOneBesselTransform W) j (K*y) := by
  have he : (fun t : ℝ ↦ weightOneBesselTransform (fun x ↦ W (x/K)) (y*Real.exp t)) =
      fun t : ℝ ↦ (K : ℂ)*weightOneBesselTransform W ((K*y)*Real.exp t) := by
    funext t
    rw [weightOneBesselTransform_dilate W K _ hK]
    congr 1
    congr 1
    ring
  have hsm := weightOneBesselTransform_log_smooth W B hB hWs (K*y) (mul_pos hK hy)
  unfold LocalLogFourier.eulerDeriv
  rw [he]
  exact iteratedDeriv_const_mul _ (hsm.of_le (by simp)).contDiffAt

/-- Uniform dual-scale derivative control: the transition is exactly Ky≈1,
and the constants do not depend on K or y. -/
theorem weightOneBesselTransform_dilate_euler_source_bound (A J : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : SchwartzMap ℝ ℂ) (B : ℝ), 0 ≤ B → Function.support W ⊆ Icc 0 B →
        ∀ (K y : ℝ), 0 < K → 0 < y → ∀ (j : ℕ), j ≤ J →
          (1+K*y)^A *
            ‖LocalLogFourier.eulerDeriv (weightOneBesselTransform (fun x ↦ W (x/K))) j y‖ ≤
              C*K*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  obtain ⟨s,C,hC,hb⟩ := weightOneBesselTransform_euler_source_bound A J
  refine ⟨s,C,hC,?_⟩
  intro W B hB hWs K y hK hy j hj
  rw [weightOneBesselTransform_dilate_euler W B hB hWs K y hK hy j,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hK]
  have hx := mul_le_mul_of_nonneg_left (hb W B hB hWs j hj (K*y) (mul_pos hK hy)) hK.le
  nlinarith

end ArtinMatthews
