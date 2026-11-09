module

public import ArtinMatthews.VaryingKummerAnalyticMixedMellinResidues


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute convergence and degree/discriminant-uniform control of the full
left vertical integral in the actual smoothed Dedekind explicit formula. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex MeasureTheory Set Filter
open scoped Classical Topology ContDiff
noncomputable section
universe u

def mixedMellinLeftLine (t : ℝ) : ℂ := (-(1/2 : ℝ) : ℂ)+(t : ℂ)*I

@[simp] theorem mixedMellinLeftLine_re (t : ℝ) : (mixedMellinLeftLine t).re = -(1/2 : ℝ) := by
  simp [mixedMellinLeftLine]
@[simp] theorem mixedMellinLeftLine_im (t : ℝ) : (mixedMellinLeftLine t).im = t := by
  simp [mixedMellinLeftLine]

theorem smoothMellin_left_mass_integrable (f : ℝ → ℂ) (hcompact : HasCompactSupport f)
    (hpositive : tsupport f ⊆ Ioi 0) (hsmooth : ContDiff ℝ ∞ f) :
    Integrable (fun t : ℝ => (1+|t|)*‖mellin f (mixedMellinLeftLine t)‖) := by
  let S := OAI.CubicFirstMoment.mellinVerticalSchwartz f hcompact hpositive hsmooth (-(1/2))
  have h0 : Integrable (fun t : ℝ => ‖S t‖) := S.integrable.norm
  have h1 := S.integrable_pow_mul volume 1
  have heS (t : ℝ) : S t = mellin f (mixedMellinLeftLine t) := by
    simpa only [S,mixedMellinLeftLine,Complex.ofReal_neg,Complex.ofReal_div,
      Complex.ofReal_one,Complex.ofReal_ofNat] using
      OAI.CubicFirstMoment.mellinVerticalSchwartz_apply f hcompact hpositive hsmooth (-(1/2)) t
  have hsum : Integrable (fun t : ℝ => ‖S t‖+|t| * ‖S t‖) :=
    h0.add (by simpa only [Real.norm_eq_abs,pow_one] using h1)
  apply hsum.congr
  filter_upwards with t
  rw [heS]
  ring

theorem mixedExplicitFormulaIntegrand_left_continuous
    (K : Type u) [Field K] [NumberField K] (f : ℝ → ℂ)
    (hcompact : HasCompactSupport f) (hpositive : tsupport f ⊆ Ioi 0)
    (hcontinuous : Continuous f) {x : ℝ} (hx : 0<x) :
    Continuous (fun t : ℝ => mixedExplicitFormulaIntegrand K f x (mixedMellinLeftLine t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hza := mixedDedekindZeta_analyticAt K (s := mixedMellinLeftLine t) (by
    intro h
    have H := congrArg Complex.re h
    norm_num at H)
  have hlog := (hza.deriv.div hza (mixedDedekindZeta_left_ne_zero K
    (mixedMellinLeftLine_re t))).continuousAt
  have hW := ((smoothMellin_entire f hcompact hpositive hcontinuous).mul
    (differentiable_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))))
  have H := ((hW (mixedMellinLeftLine t)).neg.continuousAt).mul hlog
  exact H.comp (by unfold mixedMellinLeftLine; fun_prop : ContinuousAt mixedMellinLeftLine t)

/-- The integral bound needed after the contour shift. The constant depends
only on the fixed smooth compact weight, not on the number field or x. -/
theorem exists_mixedMellin_left_integral_bound
    (f : ℝ → ℂ) (hcompact : HasCompactSupport f) (hpositive : tsupport f ⊆ Ioi 0)
    (hsmooth : ContDiff ℝ ∞ f) :
    ∃ A : ℝ,0<A ∧ ∀ (K : Type u) [Field K] [NumberField K],∀ x : ℝ,0<x →
      Integrable (fun t : ℝ => mixedExplicitFormulaIntegrand K f x (mixedMellinLeftLine t)) ∧
      ‖((1/(2*Real.pi) : ℝ) : ℂ)*
        ∫ t : ℝ,mixedExplicitFormulaIntegrand K f x (mixedMellinLeftLine t)‖ ≤
        A*x^(-(1/2 : ℝ))*(Real.log |(discr K : ℝ)|+(Module.finrank ℚ K : ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := exists_mixedDedekindZeta_left_bound.{u}
  let m : ℝ → ℝ := fun t => (1+|t|)*‖mellin f (mixedMellinLeftLine t)‖
  have hm : Integrable m := smoothMellin_left_mass_integrable f hcompact hpositive hsmooth
  let J : ℝ := ∫ t : ℝ,m t
  have hJ : 0≤J := integral_nonneg (fun t => by dsimp [m]; positivity)
  refine ⟨C*(J+1),by positivity,?_⟩
  intro K _ _ x hx
  let d := Real.log |(discr K : ℝ)|
  let n : ℝ := Module.finrank ℚ K
  have hd : 0≤d := discr_log_nonneg K
  have hn : 0≤n := Nat.cast_nonneg _
  have hxp : 0<x^(-(1/2 : ℝ)) := Real.rpow_pos_of_pos hx _
  let B := C*x^(-(1/2 : ℝ))*(d+n)
  have hB : 0≤B := by dsimp [B]; positivity
  have hb (t : ℝ) : ‖mixedExplicitFormulaIntegrand K f x (mixedMellinLeftLine t)‖ ≤ B*m t := by
    have hz := hbound K (mixedMellinLeftLine t) (mixedMellinLeftLine_re t)
    simp only [mixedMellinLeftLine_im] at hz
    have hlog : Real.log (|t|+2) ≤ |t|+1 := by
      have H := Real.log_le_sub_one_of_pos (by positivity : 0 < |t|+2)
      linarith
    have hpoly : d+n*Real.log (|t|+2) ≤ (d+n)*(1+|t|) := by
      nlinarith [mul_le_mul_of_nonneg_left hlog hn,mul_nonneg hd (abs_nonneg t)]
    have hzn : ‖logDeriv (mixedDedekindZeta K) (mixedMellinLeftLine t)‖ ≤
        C*((d+n)*(1+|t|)) := hz.trans (mul_le_mul_of_nonneg_left hpoly hC.le)
    unfold mixedExplicitFormulaIntegrand
    rw [norm_mul,norm_neg,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hx,mixedMellinLeftLine_re]
    calc
      _ ≤ (‖mellin f (mixedMellinLeftLine t)‖*x^(-(1/2 : ℝ)))*(C*((d+n)*(1+|t|))) :=
        mul_le_mul_of_nonneg_left hzn (by positivity)
      _ = _ := by dsimp [B,m]; ring
  have hc := mixedExplicitFormulaIntegrand_left_continuous K f hcompact hpositive hsmooth.continuous hx
  have hi : Integrable (fun t : ℝ => mixedExplicitFormulaIntegrand K f x (mixedMellinLeftLine t)) :=
    (hm.const_mul B).mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  refine ⟨hi,?_⟩
  have hnorm : ‖∫ t : ℝ,mixedExplicitFormulaIntegrand K f x (mixedMellinLeftLine t)‖ ≤ B*J := by
    calc
      _ ≤ ∫ t : ℝ,‖mixedExplicitFormulaIntegrand K f x (mixedMellinLeftLine t)‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ,B*m t := integral_mono_ae hi.norm (hm.const_mul B) (Filter.Eventually.of_forall hb)
      _ = B*J := integral_const_mul _ _
  have hp : ‖((1/(2*Real.pi) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    apply (div_le_one (by positivity : 0<2*Real.pi)).mpr
    linarith [Real.pi_gt_three]
  rw [norm_mul]
  calc
    _ ≤ ‖∫ t : ℝ,mixedExplicitFormulaIntegrand K f x (mixedMellinLeftLine t)‖ :=
      mul_le_of_le_one_left (norm_nonneg _) hp
    _ ≤ B*J := hnorm
    _ ≤ _ := by dsimp [B,d,n]; nlinarith [mul_nonneg hB (by norm_num : (0 : ℝ)≤1)]

end
end ArtinMatthews.VaryingKummerAnalytic
