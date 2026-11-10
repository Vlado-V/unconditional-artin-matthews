module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev


set_option backward.privateInPublic true
@[expose] public section

/-! Quantitative Fourier decay from the actual zeroth and jth derivative
L1 norms. This preserves the explicit moving-transition width. -/

noncomputable section
namespace ArtinMatthews
open MeasureTheory
open scoped ContDiff FourierTransform

theorem heckeFourier_derivative_power_bound (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (j : ℕ) (t : ℝ) :
    |t|^j*‖𝓕 f t‖ ≤ (∫ s : ℝ, ‖iteratedDeriv j f s‖)/(2*Real.pi)^j := by
  have hcs (k : ℕ) : HasCompactSupport (iteratedDeriv k f) := by
    induction k with
    | zero => simpa only [iteratedDeriv_zero] using hc
    | succ k ih => simpa only [iteratedDeriv_succ] using ih.deriv
  have hi (k : ℕ) : Integrable (iteratedDeriv k f) :=
    (hf.continuous_iteratedDeriv k (by simp)).integrable_of_hasCompactSupport (hcs k)
  have hfour := Real.fourier_iteratedDeriv (N := (⊤ : ℕ∞)) hf
    (fun k _ => hi k) (by simp : (j : ℕ∞) ≤ ⊤)
  have hid : (2*Real.pi)^j*(|t|^j*‖𝓕 f t‖) = ‖𝓕 (iteratedDeriv j f) t‖ := by
    rw [hfour]
    simp only [norm_smul, norm_pow, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
    ring
  have hnorm := VectorFourier.norm_fourierIntegral_le_integral_norm
    Real.fourierChar volume (innerₗ ℝ) (iteratedDeriv j f) t
  apply (le_div_iff₀ (by positivity : 0 < (2*Real.pi)^j)).mpr
  rw [mul_comm, hid]
  exact hnorm

theorem heckeFourier_weighted_derivative_bound (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (j : ℕ) (t : ℝ) :
    (1+|t|)^j*‖𝓕 f t‖ ≤ (2 : ℝ)^j*
      ((∫ s : ℝ, ‖f s‖)+(∫ s : ℝ, ‖iteratedDeriv j f s‖)/(2*Real.pi)^j) := by
  have h0 : ‖𝓕 f t‖ ≤ ∫ s : ℝ, ‖f s‖ :=
    VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume (innerₗ ℝ) f t
  have hj := heckeFourier_derivative_power_bound f hf hc j t
  have hI0 : 0 ≤ ∫ s : ℝ, ‖f s‖ := integral_nonneg (fun s => norm_nonneg _)
  have hIj : 0 ≤ (∫ s : ℝ, ‖iteratedDeriv j f s‖)/(2*Real.pi)^j :=
    div_nonneg (integral_nonneg (fun s => norm_nonneg _)) (by positivity)
  by_cases ht : |t| ≤ 1
  · calc
      _ ≤ (2 : ℝ)^j*‖𝓕 f t‖ := by gcongr; linarith
      _ ≤ (2 : ℝ)^j*(∫ s : ℝ, ‖f s‖) := mul_le_mul_of_nonneg_left h0 (by positivity)
      _ ≤ _ := by gcongr; linarith
  · have ht' : 1 ≤ |t| := le_of_lt (lt_of_not_ge ht)
    calc
      _ ≤ (2*|t|)^j*‖𝓕 f t‖ := by gcongr; linarith
      _ = (2 : ℝ)^j*(|t|^j*‖𝓕 f t‖) := by rw [mul_pow, mul_assoc]
      _ ≤ (2 : ℝ)^j*((∫ s : ℝ, ‖iteratedDeriv j f s‖)/(2*Real.pi)^j) :=
        mul_le_mul_of_nonneg_left hj (by positivity)
      _ ≤ _ := by gcongr; linarith

theorem heckeFourier_transition_width_bound (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (j : ℕ)
    {ε C₀ Cj : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hC₀ : 0 ≤ C₀)
    (h0 : (∫ s : ℝ, ‖f s‖) ≤ C₀)
    (hj : (∫ s : ℝ, ‖iteratedDeriv j f s‖) ≤ Cj/ε^j) (t : ℝ) :
    (1+|t|)^j*‖𝓕 f t‖ ≤ ((2 : ℝ)^j*(C₀+Cj/(2*Real.pi)^j))/ε^j := by
  have hεj : ε^j ≤ 1 := pow_le_one₀ hε.le hε1
  have hC0 : C₀ ≤ C₀/ε^j := by
    apply (le_div_iff₀ (pow_pos hε j)).mpr
    exact mul_le_of_le_one_right hC₀ hεj
  apply (heckeFourier_weighted_derivative_bound f hf hc j t).trans
  calc
    _ ≤ (2 : ℝ)^j*(C₀/ε^j+(Cj/ε^j)/(2*Real.pi)^j) := by
      gcongr
      exact h0.trans hC0
    _ = _ := by ring

end ArtinMatthews
