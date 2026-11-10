module

public import Mathlib.Analysis.SpecialFunctions.Bessel
public import Mathlib.RingTheory.Polynomial.ShiftedLegendre
public import ArtinMatthews.ShiftedLegendreMoments
public import ArtinMatthews.ShiftedVoronoiBessel
public import Mathlib.Analysis.Calculus.Deriv.Polynomial


set_option backward.privateInPublic true
@[expose] public section

/-! The actual order-zero Bessel factorial series may be integrated
against a shifted Legendre polynomial on the unit interval. -/
namespace ArtinMatthews
open Complex MeasureTheory Set Polynomial
open scoped Polynomial Interval

noncomputable section

def spectralLegendreValue (n : ℕ) (u : ℝ) : ℝ :=
  aeval u (shiftedLegendre n)

theorem spectralLegendreValue_continuous (n : ℕ) :
    Continuous (spectralLegendreValue n) :=
  (shiftedLegendre n).differentiable_aeval.continuous

theorem spectralLegendreValue_unit_bound (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u ∈ Icc (0 : ℝ) 1, ‖spectralLegendreValue n u‖ ≤ M := by
  obtain ⟨M,hM⟩ := (isCompact_Icc.image (spectralLegendreValue_continuous n).norm).bddAbove
  exact ⟨max 0 M, le_max_left _ _,
    fun u hu => (hM ⟨u,hu,rfl⟩).trans (le_max_right _ _)⟩

theorem spectral_besselJ_zero_sqrt_argument (x u : ℝ) (hx : 0 ≤ x) :
    (x : ℂ) * (Real.sqrt u : ℂ) = 2 * (Real.sqrt ((x/2)^2 * u) : ℂ) := by
  rw [Real.sqrt_mul (sq_nonneg (x/2)), Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  push_cast
  ring

def spectralLegendreBesselTerm (n : ℕ) (x : ℝ) (m : ℕ) (u : ℝ) : ℂ :=
  (((-((x / 2) ^ 2)) ^ m / (m.factorial : ℝ) ^ 2) *
    (u ^ m * spectralLegendreValue n u) : ℝ)

private theorem spectralLegendreBesselTerm_continuous (n : ℕ) (x : ℝ) (m : ℕ) :
    Continuous (spectralLegendreBesselTerm n x m) := by
  apply Complex.continuous_ofReal.comp
  exact continuous_const.mul ((continuous_id.pow m).mul (spectralLegendreValue_continuous n))

private theorem spectralLegendreBesselTerm_hasSum (n : ℕ) (x u : ℝ)
    (hx : 0 ≤ x) (hu : 0 ≤ u) :
    HasSum (fun m : ℕ => spectralLegendreBesselTerm n x m u)
      ((spectralLegendreValue n u : ℂ) * Complex.besselJ 0 ((x : ℂ) * Real.sqrt u)) := by
  rw [spectral_besselJ_zero_sqrt_argument x u hx]
  have hs := (hasSum_besselJ_zero_sqrt ((x/2)^2*u) (by positivity)).mul_left
    (spectralLegendreValue n u : ℂ)
  convert hs using 1
  funext m
  simp only [spectralLegendreBesselTerm, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_natCast, ← neg_mul, mul_pow]
  ring

private theorem spectralLegendreBesselTerm_norm_le (n : ℕ) (x : ℝ) (m : ℕ)
    (M u : ℝ) (hM : 0 ≤ M) (hu : u ∈ Icc (0 : ℝ) 1)
    (hP : ‖spectralLegendreValue n u‖ ≤ M) :
    ‖spectralLegendreBesselTerm n x m u‖ ≤ M * (((x/2)^2)^m / (m.factorial : ℝ)) := by
  let t : ℝ := (x/2)^2
  have ht : 0 ≤ t := by positivity
  have hf : (1 : ℝ) ≤ m.factorial := by
    exact_mod_cast (Nat.factorial_pos m)
  have hf0 : (0 : ℝ) ≤ m.factorial := Nat.cast_nonneg _
  have hu' : u ^ m ≤ 1 := pow_le_one₀ hu.1 hu.2
  have hnorm :
      ‖spectralLegendreBesselTerm n x m u‖ =
        t ^ m / (m.factorial : ℝ) ^ 2 * (u ^ m * ‖spectralLegendreValue n u‖) := by
    change ‖(((-t)^m / (m.factorial : ℝ)^2 * (u^m * spectralLegendreValue n u) : ℝ) : ℂ)‖ = _
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_div, abs_pow, abs_neg,
      abs_of_nonneg ht, abs_of_nonneg hu.1, abs_of_nonneg hf0]
  have hf2 : (m.factorial : ℝ) ≤ (m.factorial : ℝ)^2 := by nlinarith
  have hcoeff : t^m / (m.factorial : ℝ)^2 ≤ t^m / (m.factorial : ℝ) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hf2
  calc
    _ = t ^ m / (m.factorial : ℝ) ^ 2 * (u ^ m * ‖spectralLegendreValue n u‖) := hnorm
    _ ≤ (t ^ m / (m.factorial : ℝ)) * (1 * M) :=
      mul_le_mul hcoeff (mul_le_mul hu' hP (norm_nonneg _) zero_le_one)
        (mul_nonneg (pow_nonneg hu.1 _) (norm_nonneg _)) (div_nonneg (pow_nonneg ht _) hf0)
    _ = _ := by ring

theorem spectralLegendreBesselTerm_interval_hasSum (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    HasSum (fun m : ℕ => ∫ u in (0 : ℝ)..1, spectralLegendreBesselTerm n x m u)
      (∫ u in (0 : ℝ)..1, (spectralLegendreValue n u : ℂ) *
        Complex.besselJ 0 ((x : ℂ) * (Real.sqrt u : ℂ))) := by
  obtain ⟨M,hM,hP⟩ := spectralLegendreValue_unit_bound n
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun m _ => M * (((x/2)^2)^m / (m.factorial : ℝ))) ?_ ?_ ?_ ?_ ?_
  · intro m
    exact (spectralLegendreBesselTerm_continuous n x m).aestronglyMeasurable
  · intro m
    filter_upwards with u hu
    rw [uIoc_of_le zero_le_one] at hu
    exact spectralLegendreBesselTerm_norm_le n x m M u hM ⟨hu.1.le,hu.2⟩
      (hP u ⟨hu.1.le,hu.2⟩)
  · filter_upwards with u hu
    exact (NormedSpace.expSeries_div_hasSum_exp ((x/2)^2)).summable.mul_left M
  · exact intervalIntegrable_const
  · filter_upwards with u hu
    rw [uIoc_of_le zero_le_one] at hu
    exact spectralLegendreBesselTerm_hasSum n x u hx hu.1.le

theorem spectralLegendreBesselTerm_interval (n : ℕ) (x : ℝ) (m : ℕ) :
    (∫ u in (0 : ℝ)..1, spectralLegendreBesselTerm n x m u) =
      (((-((x/2)^2))^m / (m.factorial : ℝ)^2) *
        ((-1 : ℝ)^n * ((m.descFactorial n * m.factorial : ℕ) : ℝ) /
          ((m+n+1).factorial : ℝ)) : ℝ) := by
  unfold spectralLegendreBesselTerm
  rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul]
  congr 2
  exact integral_pow_shiftedLegendre n m

end
end ArtinMatthews
