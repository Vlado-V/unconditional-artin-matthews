module

public import Mathlib.Analysis.Complex.CanonicalDecomposition
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! Polynomial factors of the finite Blaschke quotient used in the disk
estimate. Their logarithmic derivatives retain the literal zero terms. -/

@[expose] public section

namespace ArtinMatthews

open Complex Metric Set
open scoped BigOperators

noncomputable def independentDiskMirror (R : ℝ) (a z : ℂ) : ℂ :=
  ((R : ℂ)^2 - star a * z) / R

def independentDiskVanishing (S : Finset ℂ) (m : ℂ → ℕ) (z : ℂ) : ℂ :=
  ∏ a ∈ S, (z - a) ^ m a

noncomputable def independentDiskDenominator (R : ℝ) (S : Finset ℂ) (m : ℂ → ℕ) (z : ℂ) : ℂ :=
  ∏ a ∈ S, independentDiskMirror R a z ^ m a

theorem independentDiskMirror_analytic (R : ℝ) (a z : ℂ) :
    AnalyticAt ℂ (independentDiskMirror R a) z := by
  have hd : AnalyticAt ℂ (fun w : ℂ => (R : ℂ)^2 - star a * w) z :=
    analyticAt_const.sub (analyticAt_const.mul analyticAt_id)
  exact hd.div_const

theorem independentDiskVanishing_analytic (S : Finset ℂ) (m : ℂ → ℕ) (z : ℂ) :
    AnalyticAt ℂ (independentDiskVanishing S m) z :=
  S.analyticAt_fun_prod fun _ _ => (analyticAt_id.sub analyticAt_const).pow _

theorem independentDiskDenominator_analytic (R : ℝ) (S : Finset ℂ) (m : ℂ → ℕ) (z : ℂ) :
    AnalyticAt ℂ (independentDiskDenominator R S m) z :=
  S.analyticAt_fun_prod fun _ _ => (independentDiskMirror_analytic _ _ _).pow _

theorem independentDiskVanishing_ne_zero {S : Finset ℂ} (m : ℂ → ℕ)
    {z : ℂ} (hz : z ∉ S) : independentDiskVanishing S m z ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro a ha
  exact pow_ne_zero _ (sub_ne_zero.mpr (fun h => hz (h ▸ ha)))

private theorem diskMirror_unscaled_ne_zero {R : ℝ} (hR : 0 < R) {a z : ℂ}
    (ha : ‖a‖ < R) (hz : ‖z‖ ≤ R) : (R : ℂ)^2 - star a * z ≠ 0 := by
  have hlt : ‖star a * z‖ < R^2 := by
    rw [norm_mul, norm_star, pow_two]
    exact (mul_le_mul_of_nonneg_left hz (norm_nonneg _)).trans_lt
      (mul_lt_mul_of_pos_right ha hR)
  intro h
  have heq := congrArg norm (sub_eq_zero.mp h)
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR] at heq
  exact hlt.ne heq.symm

theorem independentDiskMirror_ne_zero {R : ℝ} (hR : 0 < R) {a z : ℂ}
    (ha : ‖a‖ < R) (hz : ‖z‖ ≤ R) : independentDiskMirror R a z ≠ 0 :=
  div_ne_zero (diskMirror_unscaled_ne_zero hR ha hz) (Complex.ofReal_ne_zero.mpr hR.ne')

theorem independentDiskDenominator_ne_zero {R : ℝ} (hR : 0 < R)
    {S : Finset ℂ} (m : ℂ → ℕ) (hS : ∀ a ∈ S, ‖a‖ < R)
    {z : ℂ} (hz : ‖z‖ ≤ R) : independentDiskDenominator R S m z ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  exact fun a ha => pow_ne_zero _ (independentDiskMirror_ne_zero hR (hS a ha) hz)

private theorem diskMirror_norm_circle {R : ℝ} (hR : 0 < R) {a z : ℂ}
    (ha : ‖a‖ < R) (hz : z ∈ sphere 0 R) :
    ‖independentDiskMirror R a z‖ = ‖z - a‖ := by
  have hza : z - a ≠ 0 := by
    intro h
    have heq := mem_sphere_zero_iff_norm.mp hz
    rw [sub_eq_zero.mp h] at heq
    exact ha.ne heq
  have h := Complex.norm_canonicalFactor_eval_circle_eq_one (mem_ball_zero_iff.mpr ha) hz
  rw [Complex.canonicalFactor_apply, norm_div, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hR] at h
  have heq : ‖(R : ℂ)^2 - star a * z‖ = 1 * (R * ‖z - a‖) := by
    simpa only [starRingEnd_apply] using
      (div_eq_iff (mul_ne_zero hR.ne' (norm_ne_zero_iff.mpr hza))).mp h
  rw [independentDiskMirror, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hR, heq, one_mul, mul_comm R, mul_div_cancel_right₀ _ hR.ne']

theorem independentDiskDenominator_norm_circle {R : ℝ} (hR : 0 < R)
    {S : Finset ℂ} (m : ℂ → ℕ) (hS : ∀ a ∈ S, ‖a‖ < R)
    {z : ℂ} (hz : z ∈ sphere 0 R) :
    ‖independentDiskDenominator R S m z‖ = ‖independentDiskVanishing S m z‖ := by
  simp only [independentDiskDenominator, independentDiskVanishing, norm_prod, norm_pow]
  exact Finset.prod_congr rfl fun a ha => by rw [diskMirror_norm_circle hR (hS a ha) hz]

theorem independentDiskVanishing_norm_zero_le {R : ℝ} (hR : 0 < R)
    {S : Finset ℂ} (m : ℂ → ℕ) (hS : ∀ a ∈ S, ‖a‖ ≤ R) :
    ‖independentDiskVanishing S m 0‖ ≤ ‖independentDiskDenominator R S m 0‖ := by
  simp only [independentDiskVanishing, independentDiskDenominator, norm_prod, norm_pow]
  apply Finset.prod_le_prod₀ (fun _ _ => pow_nonneg (norm_nonneg _) _)
  intro a ha
  have hD : independentDiskMirror R a 0 = (R : ℂ) := by
    simp only [independentDiskMirror, mul_zero, sub_zero, pow_two,
      mul_div_cancel_right₀ _ (Complex.ofReal_ne_zero.mpr hR.ne')]
  rw [zero_sub, norm_neg, hD, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  exact pow_le_pow_left₀ (norm_nonneg _) (hS a ha) _

theorem independentDiskVanishing_logDeriv {S : Finset ℂ} (m : ℂ → ℕ)
    {z : ℂ} (hz : z ∉ S) :
    logDeriv (independentDiskVanishing S m) z =
      ∑ a ∈ S, (m a : ℂ) / (z - a) := by
  unfold independentDiskVanishing
  rw [logDeriv_fun_prod]
  · refine Finset.sum_congr rfl fun a _ => ?_
    have hd : HasDerivAt (fun w : ℂ => w - a) 1 z := (hasDerivAt_id z).sub_const a
    rw [logDeriv_fun_pow hd.differentiableAt, logDeriv_apply, hd.deriv]
    rw [mul_one_div]
  · intro a ha
    exact pow_ne_zero _ (sub_ne_zero.mpr (fun h => hz (h ▸ ha)))
  · intro a _
    exact ((hasDerivAt_id z).sub_const a).differentiableAt.pow _

private theorem diskMirror_logDeriv {R : ℝ} (hR : 0 < R) (a z : ℂ) :
    logDeriv (independentDiskMirror R a) z =
      -star a / ((R : ℂ)^2 - star a * z) := by
  have hd : HasDerivAt (independentDiskMirror R a) (-star a / (R : ℂ)) z := by
    change HasDerivAt (fun w : ℂ => ((R : ℂ)^2 - star a * w) / (R : ℂ)) _ z
    simpa only [Pi.sub_apply, Pi.mul_apply, id_eq, zero_sub, mul_one] using
      (((hasDerivAt_const z ((R : ℂ)^2)).sub
        ((hasDerivAt_id z).const_mul (star a))).div_const (R : ℂ))
  rw [logDeriv_apply, hd.deriv, independentDiskMirror,
    div_div_div_cancel_right₀ (Complex.ofReal_ne_zero.mpr hR.ne')]

private theorem diskMirror_logDeriv_norm_le {R R1 : ℝ} (hR1 : 0 < R1)
    (hRR1 : R1 < R) {a z : ℂ} (ha : ‖a‖ ≤ R1) (hz : ‖z‖ ≤ R1) :
    ‖logDeriv (independentDiskMirror R a) z‖ ≤ 1 / (R^2 / R1 - R1) := by
  have hR := hR1.trans hRR1
  have hd := norm_sub_norm_le ((R : ℂ)^2) (star a * z)
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, norm_mul, norm_star] at hd
  have hp : ‖a‖ * ‖z‖ ≤ R1^2 := by
    rw [pow_two]
    exact mul_le_mul ha hz (norm_nonneg _) hR1.le
  have hdiff : 0 < R^2 - R1^2 := by
    nlinarith [mul_pos (sub_pos.mpr hRR1) (add_pos hR hR1)]
  have hd' : R^2 - R1^2 ≤ ‖(R : ℂ)^2 - star a * z‖ := by linarith
  rw [diskMirror_logDeriv hR, norm_div, norm_neg, norm_star]
  calc
    ‖a‖ / ‖(R : ℂ)^2 - star a * z‖ ≤ R1 / ‖(R : ℂ)^2 - star a * z‖ :=
      div_le_div_of_nonneg_right ha (norm_nonneg _)
    _ ≤ R1 / (R^2 - R1^2) := div_le_div_of_nonneg_left hR1.le hdiff hd'
    _ = 1 / (R^2 / R1 - R1) := by
      have he : R^2 / R1 - R1 = (R^2 - R1^2) / R1 := by
        field_simp
      rw [he, one_div_div]

theorem independentDiskDenominator_logDeriv_bound {R R1 : ℝ} (hR1 : 0 < R1)
    (hRR1 : R1 < R) {S : Finset ℂ} (m : ℂ → ℕ) (hS : ∀ a ∈ S, ‖a‖ ≤ R1)
    {z : ℂ} (hz : ‖z‖ ≤ R1) :
    ‖logDeriv (independentDiskDenominator R S m) z‖ ≤
      (∑ a ∈ S, (m a : ℝ)) * (1 / (R^2 / R1 - R1)) := by
  have hR := hR1.trans hRR1
  have hd (a : ℂ) := (independentDiskMirror_analytic R a z).differentiableAt
  unfold independentDiskDenominator
  rw [logDeriv_fun_prod]
  · simp_rw [logDeriv_fun_pow (hd _)]
    calc
      ‖∑ a ∈ S, (m a : ℂ) * logDeriv (independentDiskMirror R a) z‖ ≤
          ∑ a ∈ S, ‖(m a : ℂ) * logDeriv (independentDiskMirror R a) z‖ :=
        norm_sum_le _ _
      _ ≤ ∑ a ∈ S, (m a : ℝ) * (1 / (R^2 / R1 - R1)) := by
        refine Finset.sum_le_sum fun a ha => ?_
        rw [norm_mul, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_left (diskMirror_logDeriv_norm_le hR1 hRR1 (hS a ha) hz)
          (Nat.cast_nonneg _)
      _ = _ := by rw [Finset.sum_mul]
  · exact fun a ha => pow_ne_zero _ (independentDiskMirror_ne_zero hR
      ((hS a ha).trans_lt hRR1) (hz.trans hRR1.le))
  · exact fun a _ => (hd a).pow _

end ArtinMatthews
