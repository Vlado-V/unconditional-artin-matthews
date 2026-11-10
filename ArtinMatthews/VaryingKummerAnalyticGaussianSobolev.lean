module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial


set_option backward.privateInPublic true
@[expose] public section

/-! A geometry-independent local height estimate.  A complex function and
its actual derivative control every point of a unit height window by their
Gaussian square masses.  This is the analytic maximal step used before
applying the actual general-field conductor sieve. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open MeasureTheory Set
open scoped RealInnerProductSpace
noncomputable section

theorem norm_sq_le_local_derivative_energy {F F' : ℝ → ℂ}
    (hF : ∀ t, HasDerivAt F (F' t) t) (hF' : Continuous F') (s : ℝ) :
    ‖F s‖^2 ≤ 2 * ∫ t in s..s+1, (‖F t‖^2 + ‖F' t‖^2) := by
  have hc : Continuous F := continuous_iff_continuousAt.mpr fun t => (hF t).continuousAt
  let E : ℝ → ℝ := fun t => ‖F t‖^2 + ‖F' t‖^2
  have he : Continuous E := (hc.norm.pow 2).add (hF'.norm.pow 2)
  have hnonneg : ∀ t, 0 ≤ E t := fun t => add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hpoint (u : ℝ) (hu : u ∈ Icc s (s+1)) :
      ‖F s‖^2 ≤ ‖F u‖^2 + ∫ t in s..s+1, E t := by
    have hdiff : -(‖F u‖^2) - -(‖F s‖^2) ≤ ∫ t in s..u, E t := by
      apply intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hu.1
        (hc.norm.pow 2 |>.neg.continuousOn)
        (fun t _ => (hF t).norm_sq.neg.hasDerivWithinAt) he.integrableOn_Icc
      intro t _
      have hi : -(inner ℝ (F t) (F' t)) ≤ ‖F t‖ * ‖F' t‖ :=
        (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
      change -(2 * inner ℝ (F t) (F' t)) ≤ E t
      change -(2 * inner ℝ (F t) (F' t)) ≤ ‖F t‖^2 + ‖F' t‖^2
      nlinarith [sq_nonneg (‖F t‖-‖F' t‖)]
    have hsub : (∫ t in s..u, E t) ≤ ∫ t in s..s+1, E t := by
      apply intervalIntegral.integral_mono_interval (le_refl s) hu.1 hu.2
        (Filter.Eventually.of_forall hnonneg) (he.intervalIntegrable _ _)
    linarith
  have hlen : s+1-s = 1 := by ring
  have hav : (∫ _ in s..s+1, ‖F s‖^2) ≤
      ∫ u in s..s+1, (‖F u‖^2 + ∫ t in s..s+1, E t) :=
    intervalIntegral.integral_mono_on (show s ≤ s+1 by linarith)
    (continuous_const.intervalIntegrable s (s+1))
    ((hc.norm.pow 2 |>.add continuous_const).intervalIntegrable s (s+1)) hpoint
  have hqi : IntervalIntegrable (fun u : ℝ => ‖F u‖^2) volume s (s+1) :=
    (hc.norm.pow 2).intervalIntegrable _ _
  have hei : IntervalIntegrable (fun _ : ℝ => ∫ t in s..s+1, E t) volume s (s+1) :=
    continuous_const.intervalIntegrable _ _
  simp only [intervalIntegral.integral_add hqi hei,intervalIntegral.integral_const,
    hlen,one_smul] at hav
  have hq : (∫ t in s..s+1, ‖F t‖^2) ≤ ∫ t in s..s+1, E t :=
    intervalIntegral.integral_mono_on (by linarith)
      (hc.norm.pow 2 |>.intervalIntegrable _ _) (he.intervalIntegrable _ _)
      (fun t _ => le_add_of_nonneg_right (sq_nonneg _))
  change ‖F s‖^2 ≤ 2 * ∫ t in s..s+1, E t
  linarith

theorem norm_sq_le_gaussian_derivative_energy {F F' : ℝ → ℂ}
    (hF : ∀ t, HasDerivAt F (F' t) t) (hF' : Continuous F')
    (hg : Integrable (fun t : ℝ => Real.exp (-2*t^2) * (‖F t‖^2 + ‖F' t‖^2)))
    {s : ℝ} (hs : |s| ≤ 1) :
    ‖F s‖^2 ≤ (2 * Real.exp 8) *
      ∫ t : ℝ, Real.exp (-2*t^2) * (‖F t‖^2 + ‖F' t‖^2) := by
  have hc : Continuous F := continuous_iff_continuousAt.mpr fun t => (hF t).continuousAt
  let E : ℝ → ℝ := fun t => ‖F t‖^2 + ‖F' t‖^2
  let G : ℝ → ℝ := fun t => Real.exp (-2*t^2) * E t
  have he : Continuous E := (hc.norm.pow 2).add (hF'.norm.pow 2)
  have hgc : Continuous G := by dsimp [G]; fun_prop
  have hgn : ∀ t, 0 ≤ G t := fun t =>
    mul_nonneg (Real.exp_pos _).le (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hlocal : (∫ t in s..s+1, E t) ≤ Real.exp 8 * ∫ t in s..s+1, G t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (by linarith)
      (he.intervalIntegrable _ _) ((hgc.const_mul _).intervalIntegrable _ _)
    intro t ht
    have htsq : t^2 ≤ 4 := by
      have hs' := abs_le.mp hs
      nlinarith [ht.1,ht.2]
    have hexp : 1 ≤ Real.exp 8 * Real.exp (-2*t^2) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith)
    have hE : 0 ≤ E t := add_nonneg (sq_nonneg _) (sq_nonneg _)
    dsimp [G]
    nlinarith [mul_nonneg (sub_nonneg.mpr hexp) hE]
  have hwhole : (∫ t in s..s+1, G t) ≤ ∫ t : ℝ, G t := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    exact integral_mono_measure Measure.restrict_le_self (Filter.Eventually.of_forall hgn) hg
  have h := norm_sq_le_local_derivative_energy hF hF' s
  change ‖F s‖^2 ≤ 2 * ∫ t in s..s+1, E t at h
  change ‖F s‖^2 ≤ (2 * Real.exp 8) * ∫ t : ℝ, G t
  nlinarith [mul_le_mul_of_nonneg_left hwhole (Real.exp_pos 8).le]

end
end ArtinMatthews.VaryingKummerAnalytic
