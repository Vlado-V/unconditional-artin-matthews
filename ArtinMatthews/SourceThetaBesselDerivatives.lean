module

public import ArtinMatthews.SourceThetaBesselSchlafli
public import ArtinMatthews.SourceThetaSchlafliRecurrence
public import ArtinMatthews.SourceThetaIntegralDerivatives
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev


set_option backward.privateInPublic true
@[expose] public section

/-! The literal source03 archimedean Bessel factor has every log
derivative, exponent five-sixths at zero, and arbitrary power decay at
infinity. All derivatives come from the Schläfli integral recurrence. -/
namespace ArtinMatthews.SourceReflection

open MeasureTheory
open scoped ContDiff
noncomputable section

def sourceThetaBesselLogDerivative (c : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  (sourceThetaBesselNormalizer c : ℂ) * (sourceThetaSchlafliEuler (c ^ 2 / 4) n 0 x : ℂ)

theorem sourceThetaBesselLogDerivative_zero {c : ℝ} (hc : 0 < c) (x : ℝ) :
    sourceThetaBesselLogDerivative c 0 x = sourceThetaBesselProfile c (Real.exp x) := by
  rw [sourceThetaBesselProfile_exp_eq_moment hc x, Complex.ofReal_mul]
  rfl

theorem sourceThetaBesselLogDerivative_hasDerivAt {c : ℝ} (hc : 0 < c) (n : ℕ) (x : ℝ) :
    HasDerivAt (sourceThetaBesselLogDerivative c n) (sourceThetaBesselLogDerivative c (n + 1) x) x :=
  ((sourceThetaSchlafliEuler_hasDerivAt (sourceThetaBesselSchlafli_scale_pos hc) n 0 x).ofReal_comp).const_mul
    (sourceThetaBesselNormalizer c : ℂ)

theorem sourceThetaBesselProfile_logSmooth {c : ℝ} (hc : 0 < c) :
    ContDiff ℝ ∞ (fun x => sourceThetaBesselProfile c (Real.exp x)) := by
  rw [← funext (sourceThetaBesselLogDerivative_zero hc)]
  exact sourceThetaDerivativeFamily_contDiff (sourceThetaBesselLogDerivative c)
    (sourceThetaBesselLogDerivative_hasDerivAt hc)

theorem sourceThetaBesselProfile_logIteratedDeriv {c : ℝ} (hc : 0 < c) (n : ℕ) :
    iteratedDeriv n (fun x => sourceThetaBesselProfile c (Real.exp x)) =
      sourceThetaBesselLogDerivative c n := by
  rw [← funext (sourceThetaBesselLogDerivative_zero hc)]
  exact sourceThetaDerivativeFamily_iteratedDeriv (sourceThetaBesselLogDerivative c)
    (sourceThetaBesselLogDerivative_hasDerivAt hc) n

theorem sourceThetaBesselLogDerivative_twoEnded {c : ℝ} (hc : 0 < c) (n : ℕ)
    {A : ℝ} (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖sourceThetaBesselLogDerivative c n x‖ ≤
      C * min (Real.exp ((5 / 6 : ℝ) * x)) (Real.exp (-A * x)) := by
  obtain ⟨C, hC, hb⟩ := sourceThetaSchlafliEuler_twoEnded (sourceThetaBesselSchlafli_scale_pos hc) n 0 hA
  refine ⟨sourceThetaBesselNormalizer c * C,
    mul_nonneg (sourceThetaBesselNormalizer_pos hc).le hC, fun x => ?_⟩
  rw [sourceThetaBesselLogDerivative, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (sourceThetaBesselNormalizer_pos hc).le, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hb x) (sourceThetaBesselNormalizer_pos hc).le

/-- The physical n-th Euler derivative of the exact t K_(1/3)(c sqrt(t)). -/
def sourceThetaBesselEuler (c : ℝ) (n : ℕ) (T : ℝ) : ℂ :=
  sourceThetaBesselLogDerivative c n (Real.log T)

theorem sourceThetaBesselEuler_zero {c T : ℝ} (hc : 0 < c) (hT : 0 < T) :
    sourceThetaBesselEuler c 0 T = sourceThetaBesselProfile c T := by
  rw [sourceThetaBesselEuler, sourceThetaBesselLogDerivative_zero hc, Real.exp_log hT]

theorem sourceThetaBesselEuler_hasDerivAt {c T : ℝ} (hc : 0 < c) (hT : 0 < T) (n : ℕ) :
    HasDerivAt (sourceThetaBesselEuler c n) (T⁻¹ • sourceThetaBesselEuler c (n + 1) T) T :=
  (sourceThetaBesselLogDerivative_hasDerivAt hc n (Real.log T)).scomp T
    (Real.hasDerivAt_log hT.ne')

theorem sourceThetaBesselEuler_twoEnded {c : ℝ} (hc : 0 < c) (n : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 < T →
      ‖sourceThetaBesselEuler c n T‖ ≤ C * min (T ^ (5 / 6 : ℝ)) (T ^ (-A)) := by
  obtain ⟨C, hC, hb⟩ := sourceThetaBesselLogDerivative_twoEnded hc n hA
  refine ⟨C, hC, fun T hT => ?_⟩
  simpa only [sourceThetaBesselEuler, Real.rpow_def_of_pos hT, mul_comm (Real.log T)] using hb (Real.log T)

theorem sourceThetaBesselProfile_logDerivative_bound {c : ℝ} (hc : 0 < c) (n : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      ‖iteratedFDeriv ℝ n (fun t => sourceThetaBesselProfile c (Real.exp t)) x‖ ≤
        C * min (Real.exp ((5 / 6 : ℝ) * x)) (Real.exp (-A * x)) := by
  obtain ⟨C, hC, hb⟩ := sourceThetaBesselLogDerivative_twoEnded hc n hA
  refine ⟨C, hC, fun x => ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, sourceThetaBesselProfile_logIteratedDeriv hc]
  exact hb x

end
end ArtinMatthews.SourceReflection
