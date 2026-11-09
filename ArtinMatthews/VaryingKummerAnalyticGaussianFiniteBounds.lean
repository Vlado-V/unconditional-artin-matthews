module

public import ArtinMatthews.VaryingKummerAnalyticGaussianFiniteContour


set_option backward.privateInPublic true
@[expose] public section

/-! Exact Gaussian bounds on the finite horizontal segments and on the
remaining right-line tails. In particular the horizontal error retains
exp(-T²), while the tails retain exp(-T²/2). -/
namespace ArtinMatthews.VaryingKummerAnalytic
open MeasureTheory Set Complex
open scoped Topology
noncomputable section

def gaussianLineMass : ℝ := ∫ y : ℝ, Real.exp (-(y^2))
def gaussianHalfLineMass : ℝ := ∫ y : ℝ, Real.exp (-(y^2)/2)

theorem gaussianLineMass_nonneg : 0 ≤ gaussianLineMass := integral_nonneg (fun _ => (Real.exp_pos _).le)
theorem gaussianHalfLineMass_nonneg : 0 ≤ gaussianHalfLineMass := integral_nonneg (fun _ => (Real.exp_pos _).le)

theorem gaussian_exp_integrable : Integrable (fun y : ℝ => Real.exp (-(y^2))) := by
  simpa using integrable_exp_neg_mul_sq (b := 1) (by norm_num)

theorem gaussian_half_exp_integrable : Integrable (fun y : ℝ => Real.exp (-(y^2)/2)) := by
  have H := integrable_exp_neg_mul_sq (b := (1/2 : ℝ)) (by norm_num)
  convert H using 1
  funext y
  congr 1
  ring

theorem finiteVerticalIntegral_norm_le (F : ℂ → ℂ) {a T B : ℝ}
    (hT : 0 ≤ T) (hB : 0 ≤ B)
    (hbound : ∀ y : ℝ, |y| ≤ T → ‖F ((a : ℂ)+(y : ℂ)*I)‖ ≤ B*Real.exp (-(y^2))) :
    ‖finiteVerticalIntegral F a T‖ ≤ B*gaussianLineMass := by
  have he : Continuous (fun y : ℝ => B*Real.exp (-(y^2))) := by fun_prop
  have H := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (f := fun y : ℝ => F ((a : ℂ)+(y : ℂ)*I)) (show -T ≤ T by linarith)
    (Filter.Eventually.of_forall (fun y hy => hbound y (abs_le.mpr ⟨hy.1.le,hy.2⟩)))
    (he.intervalIntegrable (-T) T)
  rw [intervalIntegral.integral_const_mul] at H
  apply H.trans
  apply mul_le_mul_of_nonneg_left _ hB
  rw [intervalIntegral.integral_of_le (show -T ≤ T by linarith)]
  exact integral_mono_measure Measure.restrict_le_self
    (Filter.Eventually.of_forall fun y => (Real.exp_pos (-(y^2))).le) gaussian_exp_integrable

theorem finiteHorizontalError_norm_le (F : ℂ → ℂ) {a b T B : ℝ}
    (hab : a ≤ b) (hT : 0 ≤ T)
    (hbound : ∀ x ∈ Icc a b, ∀ y : ℝ, |y| ≤ T →
      ‖F ((x : ℂ)+(y : ℂ)*I)‖ ≤ B*Real.exp (-(y^2))) :
    ‖finiteHorizontalError F a b T‖ ≤ 2*B*(b-a)*Real.exp (-(T^2)) := by
  have hhor (y : ℝ) (hy : |y| ≤ T) :
      ‖finiteHorizontalIntegral F a b y‖ ≤ B*Real.exp (-(y^2))*(b-a) := by
    have H := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
      (f := fun x : ℝ => F ((x : ℂ)+(y : ℂ)*I))
      (fun x hx => hbound x (by simpa [uIcc_of_le hab] using (uIoc_subset_uIcc hx : x ∈ Set.uIcc a b)) y hy)
    simpa only [finiteHorizontalIntegral,abs_of_nonneg (sub_nonneg.mpr hab)] using H
  have hn := hhor (-T) (by simp [abs_of_nonneg hT])
  have hp := hhor T (by simp [abs_of_nonneg hT])
  rw [neg_sq] at hn
  unfold finiteHorizontalError
  rw [norm_mul,norm_I,one_mul]
  have H := norm_sub_le (finiteHorizontalIntegral F a b (-T)) (finiteHorizontalIntegral F a b T)
  nlinarith

theorem gaussian_tail_pointwise {T y : ℝ} (hT : 0 ≤ T) (hy : y ∉ Ioc (-T) T) :
    Real.exp (-(y^2)) ≤ Real.exp (-(T^2)/2)*Real.exp (-(y^2)/2) := by
  have hs : T^2 ≤ y^2 := by
    by_cases h : -T < y
    · have hy' : T < y := lt_of_not_ge (fun hyt => hy ⟨h,hyt⟩)
      nlinarith
    · have hy' : y ≤ -T := le_of_not_gt h
      nlinarith
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith)

theorem rightVerticalTail_norm_le (F : ℂ → ℂ) {b T B : ℝ}
    (hT : 0 ≤ T) (hB : 0 ≤ B)
    (hbound : ∀ y : ℝ, ‖F ((b : ℂ)+(y : ℂ)*I)‖ ≤ B*Real.exp (-(y^2))) :
    ‖rightVerticalTail F b T‖ ≤ B*gaussianHalfLineMass*Real.exp (-(T^2)/2) := by
  let g : ℝ → ℝ := fun y => (B*Real.exp (-(T^2)/2))*Real.exp (-(y^2)/2)
  have hg : Integrable g := gaussian_half_exp_integrable.const_mul _
  have hgn : ∀ y, 0 ≤ g y := by intro y; dsimp [g]; positivity
  have hpoint : ∀ᵐ (y : ℝ) ∂((volume : Measure ℝ).restrict ((Ioc (-T) T)ᶜ)),
      ‖F ((b : ℂ)+(y : ℂ)*I)‖ ≤ g y := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.compl)] with y hy
    exact (hbound y).trans (by
      dsimp [g]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (gaussian_tail_pointwise hT hy) hB)
  have H := MeasureTheory.norm_integral_le_of_norm_le hg.integrableOn hpoint
  have H' := integral_mono_measure (Measure.restrict_le_self (s := (Ioc (-T) T)ᶜ))
    (Filter.Eventually.of_forall hgn) hg
  apply (H.trans H').trans_eq
  rw [integral_const_mul]
  unfold gaussianHalfLineMass
  ring

theorem full_vertical_sub_left_norm_le (F : ℂ → ℂ) {a b T B R : ℝ}
    (hab : a ≤ b) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hF : DifferentiableOn ℂ F {z : ℂ | a ≤ z.re ∧ z.re ≤ b ∧ |z.im| ≤ T})
    (hi : Integrable (fun y : ℝ => F ((b : ℂ)+(y : ℂ)*I)))
    (hbox : ∀ x ∈ Icc a b, ∀ y : ℝ, |y| ≤ T →
      ‖F ((x : ℂ)+(y : ℂ)*I)‖ ≤ B*Real.exp (-(y^2)))
    (hright : ∀ y : ℝ, ‖F ((b : ℂ)+(y : ℂ)*I)‖ ≤ R*Real.exp (-(y^2))) :
    ‖(∫ y : ℝ, F ((b : ℂ)+(y : ℂ)*I))-finiteVerticalIntegral F a T‖ ≤
      2*B*(b-a)*Real.exp (-(T^2)) + R*gaussianHalfLineMass*Real.exp (-(T^2)/2) := by
  rw [full_vertical_finite_shift F hab hT hF hi]
  rw [show finiteVerticalIntegral F a T+finiteHorizontalError F a b T+rightVerticalTail F b T-
    finiteVerticalIntegral F a T = finiteHorizontalError F a b T+rightVerticalTail F b T by ring]
  exact (norm_add_le _ _).trans (add_le_add (finiteHorizontalError_norm_le F hab hT hbox)
    (rightVerticalTail_norm_le F hT hR hright))

end
end ArtinMatthews.VaryingKummerAnalytic
