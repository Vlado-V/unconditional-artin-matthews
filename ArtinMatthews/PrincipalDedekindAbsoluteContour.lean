module

public import ArtinMatthews.PrincipalDedekindSourceSignal


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine principal reciprocal and Gaussian contour control on every
fixed half-plane strictly to the right of one, including the manuscript's
line `1+10^-7`. No subcritical zero-free region is used. -/

namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField MeasureTheory Set Filter Complex
open OAI.SevenEighths.Continuation
open scoped NumberField Classical Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def principalRightEulerBound (a : ℝ) : ℝ :=
  Real.exp (∑' p : Nat.Primes, dedekindEulerLogMajorant K a p)

theorem principalRightEulerBound_pos (a : ℝ) : 0 < principalRightEulerBound K a :=
  Real.exp_pos _

theorem principalEulerLog_norm_le_right {a : ℝ} (ha : 1 < a)
    {s : ℂ} (hs : a ≤ s.re) :
    ‖dedekindEulerLog K s‖ ≤ ∑' p : Nat.Primes, dedekindEulerLogMajorant K a p := by
  have hm := dedekindEulerLogMajorant_summable K ha
  have hn := hm.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun p => dedekindEulerLocalLog_norm_le K p ha.le hs)
  exact (norm_tsum_le_tsum_norm hn).trans
    (hn.tsum_le_tsum (fun p => dedekindEulerLocalLog_norm_le K p ha.le hs) hm)

theorem principalSourceReciprocal_norm_le_right {a : ℝ} (ha : 1 < a)
    {s : ℂ} (hs : a ≤ s.re) :
    ‖principalSourceReciprocal K s‖ ≤ principalRightEulerBound K a := by
  rw [principalSourceReciprocal_eq_exp_neg_eulerLog K (ha.trans_le hs), Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have h := Complex.re_le_norm (-dedekindEulerLog K s)
  simp only [Complex.neg_re, norm_neg] at h
  exact h.trans (principalEulerLog_norm_le_right K ha hs)

theorem principalSourceGaussian_contour_integrals_eq
    (a b c x : ℝ) (ha : 1 < a) (hab : a ≤ b) (hx : 0 < x) :
    (∫ y : ℝ, gaussianContourIntegrand (principalSourceReciprocal K) c x ((a : ℂ)+y*I)) =
      ∫ y : ℝ, gaussianContourIntegrand (principalSourceReciprocal K) c x ((b : ℂ)+y*I) := by
  apply vertical_integral_eq_of_gaussian_bound (C :=
    max (x^(a+c)) (x^(b+c))*Real.exp ((b-5/6)^2)*principalRightEulerBound K a) _ hab
  · apply gaussianContourIntegrand_differentiableOn _ c hx
    intro z hz
    exact (principalSourceReciprocal_differentiableAt K (ha.trans_le hz.1)).differentiableWithinAt
  · intro σ hσ y
    rw [norm_gaussianContourIntegrand _ _ _ _ hx]
    have hxpow : x^(σ+c) ≤ max (x^(a+c)) (x^(b+c)) := by
      by_cases hx1 : x ≤ 1
      · exact (Real.rpow_le_rpow_of_exponent_ge hx hx1 (by linarith [hσ.1])).trans
          (le_max_left _ _)
      · exact (Real.rpow_le_rpow_of_exponent_le (le_of_lt (lt_of_not_ge hx1))
          (by linarith [hσ.2])).trans (le_max_right _ _)
    have hexp : Real.exp ((σ-5/6)^2) ≤ Real.exp ((b-5/6)^2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hσ.1,hσ.2]
    have hmax : 0 ≤ max (x^(a+c)) (x^(b+c)) :=
      (Real.rpow_nonneg hx.le _).trans (le_max_left _ _)
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    exact mul_le_mul (mul_le_mul hxpow hexp (Real.exp_pos _).le hmax)
      (principalSourceReciprocal_norm_le_right K ha (by simpa using hσ.1))
      (norm_nonneg _) (mul_nonneg hmax (Real.exp_pos _).le)

theorem principalSourceGaussianSignal_contour_eq_gt_one (c B : ℝ) (hB : 1 < B)
    {x : ℝ} (hx : 0 < x) :
    principalSourceGaussianSignal K c x = (1/(2*Real.pi) : ℂ) *
      ∫ y : ℝ, gaussianContourIntegrand (principalSourceReciprocal K) c x ((B : ℂ)+y*I) := by
  rw [principalSourceGaussianSignal_eq_contour K c hx]
  congr 1
  by_cases h : 2 ≤ B
  · exact principalSourceGaussian_contour_integrals_eq K 2 B c x (by norm_num) h hx
  · exact (principalSourceGaussian_contour_integrals_eq K B 2 c x hB (le_of_lt (lt_of_not_ge h)) hx).symm

def principalProbeSigma : ℝ := 1 + 1/10000000

theorem principalSourceGaussianSignal_contour_sigma_one (c : ℝ)
    {x : ℝ} (hx : 0 < x) :
    principalSourceGaussianSignal K c x = (1/(2*Real.pi) : ℂ) *
      ∫ y : ℝ, gaussianContourIntegrand (principalSourceReciprocal K) c x
        ((principalProbeSigma : ℂ)+y*I) :=
  principalSourceGaussianSignal_contour_eq_gt_one K c principalProbeSigma (by norm_num [principalProbeSigma]) hx

end
end ArtinMatthews.VaryingKummerAnalytic
