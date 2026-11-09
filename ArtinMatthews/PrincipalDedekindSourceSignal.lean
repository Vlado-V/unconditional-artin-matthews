module

public import ArtinMatthews.PrincipalDedekindSourceReciprocal
public import ArtinMatthews.PrincipalDedekindGaussianSignal
public import OAI.NumberTheory.DirichletL.ContinuationContour


set_option backward.privateInPublic true
@[expose] public section

/-! The principal arithmetic source signal uses the actual reciprocal of
zeta. Its exact linear relation with the pole-removed amplitude is retained. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField MeasureTheory Set Filter Asymptotics Complex
open OAI.SevenEighths.Continuation
open scoped NumberField nonZeroDivisors Classical Topology FourierTransform
noncomputable section

def principalSourceGaussianEndpointConstant (K : Type*) [Field K] [NumberField K] (B : ℝ) : ℝ :=
  ‖(1/(2*Real.pi) : ℂ)‖ * Real.exp ((B-5/6)^2) * principalSourceReciprocalBound K *
    ∫ y : ℝ, Real.exp (-(y^2))

theorem principalSourceGaussianEndpointConstant_nonneg (K : Type*) [Field K] [NumberField K]
    (B : ℝ) : 0 ≤ principalSourceGaussianEndpointConstant K B := by
  unfold principalSourceGaussianEndpointConstant
  have hg : 0 ≤ ∫ y : ℝ, Real.exp (-(y^2)) := integral_nonneg (fun _ => (Real.exp_pos _).le)
  have hC := (principalSourceReciprocalBound_pos K).le
  positivity

variable (K : Type*) [Field K] [NumberField K]

def principalSourceGaussianAmplitude (s : ℂ) : ℂ :=
  Complex.exp ((s-5/6)^2) * principalSourceReciprocal K s

def principalSourceGaussianSignal (c x : ℝ) : ℂ :=
  (x : ℂ)^(c : ℂ) * mellinInv (-2) (fun s => principalSourceGaussianAmplitude K (-s)) x

theorem principalSourceGaussianSignal_normalized (c : ℝ) {x : ℝ} (hx : 0 < x) :
    normalizedSignal (principalSourceGaussianSignal K c) c x =
      mellinInv (-2) (fun s => principalSourceGaussianAmplitude K (-s)) x := by
  unfold normalizedSignal principalSourceGaussianSignal
  simp only [smul_eq_mul,←mul_assoc]
  rw [Complex.cpow_neg,inv_mul_cancel₀]
  · simp
  · exact (Complex.cpow_eq_zero_iff _ _).not.mpr (by simp [hx.ne'])

theorem principalSourceGaussianSignal_eq_contour (c : ℝ) {x : ℝ} (hx : 0 < x) :
    principalSourceGaussianSignal K c x = (1/(2*Real.pi) : ℂ) *
      ∫ y : ℝ, gaussianContourIntegrand (principalSourceReciprocal K) c x ((2 : ℂ)+y*I) := by
  unfold principalSourceGaussianSignal mellinInv
  simp only [smul_eq_mul,Complex.real_smul,Complex.ofReal_div,Complex.ofReal_mul,
    Complex.ofReal_ofNat,Complex.ofReal_one]
  rw [mul_left_comm,←integral_const_mul]
  congr 1
  rw [←integral_neg_eq_self]
  apply integral_congr_ae
  filter_upwards [] with y
  unfold gaussianContourIntegrand principalSourceGaussianAmplitude
  have he : -(((-2 : ℝ) : ℂ)+(-y : ℝ)*I) = (2 : ℂ)+y*I := by push_cast; ring
  rw [he,←mul_assoc,←Complex.cpow_add]
  · ring_nf
  · exact Complex.ofReal_ne_zero.mpr hx.ne'


theorem principalSourceGaussianAmplitude_differentiableAt {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ (principalSourceGaussianAmplitude K) s :=
  (((differentiable_id.sub_const (5/6 : ℂ)).pow 2).cexp.differentiableAt).mul
    (principalSourceReciprocal_differentiableAt K hs)

theorem principalSourceGaussianAmplitude_continuous_line (a : ℝ) (ha : 1 < a) :
    Continuous (fun y : ℝ => principalSourceGaussianAmplitude K ((a : ℂ)+y*I)) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  have hd := principalSourceGaussianAmplitude_differentiableAt K
    (s := (a : ℂ)+y*I) (by simpa using ha)
  exact hd.continuousAt.comp (f := fun v : ℝ => (a : ℂ)+v*I)
    (by fun_prop : ContinuousAt (fun v : ℝ => (a : ℂ)+v*I) y)

theorem principalSourceGaussianAmplitude_norm_bound (a y : ℝ) (ha : 2 ≤ a) :
    ‖principalSourceGaussianAmplitude K ((a : ℂ)+y*I)‖ ≤
      (Real.exp ((a-5/6)^2)*principalSourceReciprocalBound K)*Real.exp (-(y^2)) := by
  have hn := norm_gaussianContourIntegrand (principalSourceReciprocal K) 0 a y
    (Z := 1) zero_lt_one
  simp only [gaussianContourIntegrand,Complex.ofReal_one,Complex.ofReal_zero,
    add_zero,Complex.one_cpow,one_mul,Real.one_rpow] at hn
  change ‖principalSourceGaussianAmplitude K ((a : ℂ)+y*I)‖ = _ at hn
  rw [hn]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  exact mul_le_mul_of_nonneg_left
    (principalSourceReciprocal_norm_le K (by simpa using (show (5/4 : ℝ) ≤ a by linarith)))
    (Real.exp_pos _).le

theorem principalSourceGaussianAmplitude_integrable_line (a : ℝ) (ha : 2 ≤ a) :
    Integrable (fun y : ℝ => principalSourceGaussianAmplitude K ((a : ℂ)+y*I)) :=
  integrable_of_gaussian_bound _ _
    (principalSourceGaussianAmplitude_continuous_line K a (by linarith)).aestronglyMeasurable
    (fun y => principalSourceGaussianAmplitude_norm_bound K a y ha)

theorem principalSourceGaussianSignal_contour_shift (c B : ℝ) (hB : 2 ≤ B)
    {x : ℝ} (hx : 0 < x) :
    principalSourceGaussianSignal K c x = (1/(2*Real.pi) : ℂ) *
      ∫ y : ℝ, gaussianContourIntegrand (principalSourceReciprocal K) c x ((B : ℂ)+y*I) := by
  rw [principalSourceGaussianSignal_eq_contour K c hx]
  congr 1
  apply vertical_integral_eq_of_gaussian_bound (C :=
    max (x^(2+c)) (x^(B+c))*Real.exp ((B-5/6)^2)*principalSourceReciprocalBound K) _ hB
  · apply gaussianContourIntegrand_differentiableOn _ c hx
    intro z hz
    exact (principalSourceReciprocal_differentiableAt K (by linarith [hz.1])).differentiableWithinAt
  · intro a ha y
    rw [norm_gaussianContourIntegrand _ _ _ _ hx]
    have hxpow : x^(a+c) ≤ max (x^(2+c)) (x^(B+c)) := by
      by_cases hx1 : x ≤ 1
      · exact (Real.rpow_le_rpow_of_exponent_ge hx hx1 (by linarith [ha.1])).trans
          (le_max_left _ _)
      · exact (Real.rpow_le_rpow_of_exponent_le (le_of_lt (lt_of_not_ge hx1))
          (by linarith [ha.2])).trans (le_max_right _ _)
    have hexp : Real.exp ((a-5/6)^2) ≤ Real.exp ((B-5/6)^2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [ha.1,ha.2]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    have hmax : 0 ≤ max (x^(2+c)) (x^(B+c)) :=
      (Real.rpow_nonneg hx.le _).trans (le_max_left _ _)
    have hrec : ‖principalSourceReciprocal K ((a : ℂ)+y*I)‖ ≤ principalSourceReciprocalBound K :=
      principalSourceReciprocal_norm_le K (by simpa using
        (show (5/4 : ℝ) ≤ a by linarith [ha.1]))
    exact mul_le_mul (mul_le_mul hxpow hexp (Real.exp_pos _).le hmax) hrec
      (norm_nonneg _) (mul_nonneg hmax (Real.exp_pos _).le)

theorem principalSourceGaussianSignal_bound_at_zero (c B : ℝ) (hB : 2 ≤ B)
    {x : ℝ} (hx : 0 < x) :
    ‖principalSourceGaussianSignal K c x‖ ≤ principalSourceGaussianEndpointConstant K B*x^(B+c) := by
  rw [principalSourceGaussianSignal_contour_shift K c B hB hx,norm_mul]
  have hg : Integrable (fun y : ℝ => Real.exp (-(y^2))) := by
    simpa using integrable_exp_neg_mul_sq (b := 1) (by norm_num)
  have hint := norm_integral_le_of_norm_le
    (hg.const_mul (x^(B+c)*Real.exp ((B-5/6)^2)*principalSourceReciprocalBound K))
    (f := fun y : ℝ => gaussianContourIntegrand (principalSourceReciprocal K) c x ((B : ℂ)+y*I))
    (ae_of_all _ (fun y => by
      rw [norm_gaussianContourIntegrand _ _ _ _ hx]
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact mul_le_mul_of_nonneg_left
        (principalSourceReciprocal_norm_le K (by simpa using (show (5/4 : ℝ) ≤ B by linarith)))
        (mul_nonneg (Real.rpow_nonneg hx.le _) (Real.exp_pos _).le)))
  have H := mul_le_mul_of_nonneg_left hint (norm_nonneg (1/(2*Real.pi) : ℂ))
  rw [integral_const_mul] at H
  convert H using 1
  unfold principalSourceGaussianEndpointConstant
  ring

theorem principalSourceGaussianSignal_rapidDecayAtZero (c : ℝ) :
    RapidDecayAtZero (principalSourceGaussianSignal K c) := by
  intro R
  let B : ℝ := max 2 (R-c)
  apply IsBigO.of_bound (principalSourceGaussianEndpointConstant K B)
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds
    (Iic_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with x hx hx1
  have hpow : x^(B+c) ≤ x^R := Real.rpow_le_rpow_of_exponent_ge hx hx1
    (by dsimp [B]; linarith [le_max_right (2 : ℝ) (R-c)])
  have H := (principalSourceGaussianSignal_bound_at_zero K c B (le_max_left _ _) hx).trans
    (mul_le_mul_of_nonneg_left hpow (principalSourceGaussianEndpointConstant_nonneg K B))
  simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hx.le R)] using H

theorem principalSourceGaussianAmplitude_analyticAt_one :
    AnalyticAt ℂ (principalSourceGaussianAmplitude K) 1 := by
  exact (((analyticAt_id.sub analyticAt_const).pow 2).cexp).mul
    (principalSourceReciprocal_analyticAt_one K)

theorem principalSourceGaussianAmplitude_one : principalSourceGaussianAmplitude K 1 = 0 := by
  rw [principalSourceGaussianAmplitude, principalSourceReciprocal_one, mul_zero]

theorem principalSourceGaussianAmplitude_eq_regularized (s : ℂ) :
    principalSourceGaussianAmplitude K s = (s-1) * principalGaussianAmplitude K s := by
  rw [principalSourceGaussianAmplitude, principalSourceReciprocal_eq_regularized]
  unfold principalGaussianAmplitude
  ring

end
end ArtinMatthews.VaryingKummerAnalytic
