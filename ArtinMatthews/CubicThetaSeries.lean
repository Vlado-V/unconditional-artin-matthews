module

public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-!
# Constructing holomorphic theta q-series from coefficient growth

The functions in this file are defined by convergent series, rather than by
assuming that a cusp form exists. Modularity and vanishing at all other cusps
are separate requirements not asserted here.
-/

noncomputable section
open scoped BigOperators Topology Manifold
open Complex Filter UpperHalfPlane

namespace ArtinMatthews

/-- The power series whose coefficients will be the finite ideal sums. -/
def thetaPowerSeries (a : ℕ → ℂ) (q : ℂ) : ℂ := ∑' n : ℕ, a n * q ^ n

/-- Polynomial coefficient growth suffices for convergence on the unit disk. -/
theorem theta_geometric_majorant_summable (C : ℝ) (d : ℕ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    Summable (fun n : ℕ => C * ((n : ℝ) ^ d + 1) * r ^ n) := by
  have hp : Summable (fun n : ℕ => (n : ℝ) ^ d * r ^ n) := by
    simpa only [Real.norm_eq_abs, abs_mul, abs_pow, Nat.abs_cast, abs_of_nonneg hr0] using
      summable_norm_pow_mul_geometric_of_norm_lt_one d
        (show ‖r‖ < 1 by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr)
  have hg : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_lt_one hr0 hr
  convert (hp.add hg).mul_left C using 1
  ext n
  ring

/-- Absolute convergence at each point of the unit disk. -/
theorem thetaPowerSeries_summable {a : ℕ → ℂ} {C : ℝ} {d : ℕ}
    (_hC : 0 ≤ C) (ha : ∀ n, ‖a n‖ ≤ C * ((n : ℝ) ^ d + 1))
    {q : ℂ} (hq : ‖q‖ < 1) : Summable (fun n : ℕ => a n * q ^ n) := by
  apply (theta_geometric_majorant_summable C d (norm_nonneg q) hq).of_norm_bounded
  intro n
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right (ha n) (by positivity)

/-- A polynomially bounded coefficient sequence defines a holomorphic function
on the open unit disk, proved by uniform convergence on smaller disks. -/
theorem thetaPowerSeries_differentiableAt {a : ℕ → ℂ} {C : ℝ} {d : ℕ}
    (hC : 0 ≤ C) (ha : ∀ n, ‖a n‖ ≤ C * ((n : ℝ) ^ d + 1))
    {q : ℂ} (hq : ‖q‖ < 1) : DifferentiableAt ℂ (thetaPowerSeries a) q := by
  obtain ⟨r, hqr, hr⟩ := exists_between hq
  have hr0 : 0 ≤ r := (norm_nonneg q).trans hqr.le
  have hsum := theta_geometric_majorant_summable C d hr0 hr
  have hdiff : DifferentiableOn ℂ (thetaPowerSeries a) (Metric.ball 0 r) := by
    apply differentiableOn_tsum_of_summable_norm hsum
    · intro n
      fun_prop
    · exact Metric.isOpen_ball
    · intro n z hz
      rw [norm_mul, norm_pow]
      have hz' : ‖z‖ ≤ r := (mem_ball_zero_iff.mp hz).le
      exact mul_le_mul (ha n) (pow_le_pow_left₀ (norm_nonneg z) hz' n)
        (by positivity) (by positivity)
  exact hdiff.differentiableAt (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hqr))

@[simp] theorem thetaPowerSeries_zero (a : ℕ → ℂ) : thetaPowerSeries a 0 = a 0 := by
  unfold thetaPowerSeries
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    simp [zero_pow hn]

/-- The upper-half-plane function obtained by the actual convergent q-series. -/
def thetaFromCoefficients (a : ℕ → ℂ) (τ : ℍ) : ℂ :=
  thetaPowerSeries a (Function.Periodic.qParam 1 τ)

/-- The defining Fourier series converges to the constructed theta function. -/
theorem thetaFromCoefficients_hasSum {a : ℕ → ℂ} {C : ℝ} {d : ℕ}
    (hC : 0 ≤ C) (ha : ∀ n, ‖a n‖ ≤ C * ((n : ℝ) ^ d + 1)) (τ : ℍ) :
    HasSum (fun n : ℕ => a n * Function.Periodic.qParam 1 τ ^ n)
      (thetaFromCoefficients a τ) :=
  (thetaPowerSeries_summable hC ha
    (Function.Periodic.norm_qParam_lt_one (by norm_num) τ.im_pos)).hasSum

/-- Holomorphy of the constructed upper-half-plane theta series. -/
theorem thetaFromCoefficients_mdiff {a : ℕ → ℂ} {C : ℝ} {d : ℕ}
    (hC : 0 ≤ C) (ha : ∀ n, ‖a n‖ ≤ C * ((n : ℝ) ^ d + 1)) :
    MDiff (thetaFromCoefficients a) := by
  intro τ
  have hq := (Function.Periodic.differentiable_qParam (h := (1 : ℝ))).mdifferentiable.comp
    mdifferentiable_coe
  exact (thetaPowerSeries_differentiableAt hC ha
    (Function.Periodic.norm_qParam_lt_one (by norm_num) τ.im_pos)).mdifferentiableAt.comp τ (hq τ)

/-- The q-parameter has period one. -/
theorem theta_qParam_periodic : Function.Periodic (Function.Periodic.qParam 1) (1 : ℂ) := by
  intro z
  simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one, mul_add, mul_one,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- Period one holds for the constructed series, including the totalized
extension from the upper half plane. -/
theorem thetaFromCoefficients_periodic (a : ℕ → ℂ) :
    Function.Periodic (thetaFromCoefficients a ∘ UpperHalfPlane.ofComplex) (1 : ℂ) := by
  intro z
  rcases le_or_gt z.im 0 with hz | hz
  · simp [ofComplex_apply_of_im_nonpos hz,
      ofComplex_apply_of_im_nonpos (by simpa using hz : (z + 1).im ≤ 0)]
  · simp only [Function.comp_def, ofComplex_apply_of_im_pos hz,
      ofComplex_apply_of_im_pos (by simpa using hz : 0 < (z + 1).im),
      thetaFromCoefficients, UpperHalfPlane.coe_mk, theta_qParam_periodic z]

/-- The constant coefficient is the limit at the infinite cusp. -/
theorem thetaFromCoefficients_tendsto {a : ℕ → ℂ} {C : ℝ} {d : ℕ}
    (hC : 0 ≤ C) (ha : ∀ n, ‖a n‖ ≤ C * ((n : ℝ) ^ d + 1)) :
    Tendsto (thetaFromCoefficients a) atImInfty (𝓝 (a 0)) := by
  have hcont := (thetaPowerSeries_differentiableAt hC ha (q := 0) (by norm_num)).continuousAt
  have h := hcont.tendsto.comp (qParam_tendsto_atImInfty (h := (1 : ℝ)) (by norm_num))
  rw [thetaPowerSeries_zero] at h
  exact h

/-- If the constant ideal sum vanishes, the theta series vanishes at infinity.
This makes no assertion about its other cusps. -/
theorem thetaFromCoefficients_zeroAtInfty {a : ℕ → ℂ} {C : ℝ} {d : ℕ}
    (hC : 0 ≤ C) (ha : ∀ n, ‖a n‖ ≤ C * ((n : ℝ) ^ d + 1)) (ha0 : a 0 = 0) :
    IsZeroAtImInfty (thetaFromCoefficients a) := by
  simpa only [IsZeroAtImInfty, ZeroAtFilter, ha0] using thetaFromCoefficients_tendsto hC ha

/-- The Fourier coefficients of the constructed theta series are exactly its
defining coefficients, independently of any modularity assertion. -/
theorem thetaFromCoefficients_qExpansion_coeff {a : ℕ → ℂ} {C : ℝ} {d : ℕ}
    (hC : 0 ≤ C) (ha : ∀ n, ‖a n‖ ≤ C * ((n : ℝ) ^ d + 1)) (ha0 : a 0 = 0) (n : ℕ) :
    a n = (qExpansion 1 (thetaFromCoefficients a)).coeff n := by
  have hp : Function.Periodic (thetaFromCoefficients a ∘ UpperHalfPlane.ofComplex)
      ((1 : ℝ) : ℂ) := thetaFromCoefficients_periodic a
  have hz : IsBoundedAtImInfty (thetaFromCoefficients a) :=
    (thetaFromCoefficients_zeroAtInfty hC ha ha0).isBoundedAtImInfty
  have han : AnalyticAt ℂ (cuspFunction (1 : ℝ) (thetaFromCoefficients a)) 0 :=
    analyticAt_cuspFunction_zero (by norm_num) hp (thetaFromCoefficients_mdiff hC ha) hz
  have hs : ∀ τ : ℍ, HasSum
      (fun m : ℕ => a m • Function.Periodic.qParam (1 : ℝ) τ ^ m)
      (thetaFromCoefficients a τ) := by
    intro τ
    change HasSum (fun m : ℕ => a m * Function.Periodic.qParam (1 : ℝ) τ ^ m)
      (thetaFromCoefficients a τ)
    exact thetaFromCoefficients_hasSum hC ha τ
  -- Raw function spaces have no canonical `FunLike` instance; supply the
  -- identity coercion explicitly to this polymorphic uniqueness theorem.
  exact @UpperHalfPlane.qExpansion_coeff_unique (ℍ → ℂ)
    ⟨id, Function.injective_id⟩ (1 : ℝ) (thetaFromCoefficients a) a
    (by norm_num) han hs n

end ArtinMatthews
