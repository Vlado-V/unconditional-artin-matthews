module

public import ArtinMatthews.SpectralCompactLaplaceDecay
public import ArtinMatthews.SpectralHorizontalContour


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory Complex
open scoped ContDiff
noncomputable section

theorem spectral_cosh_horizontal (t y : ℝ) :
    Complex.cosh ((t : ℂ)+(y : ℂ)*I) =
      ((Real.cosh t*Real.cos y : ℝ) : ℂ)+((Real.sinh t*Real.sin y : ℝ) : ℂ)*I := by
  rw [Complex.cosh_add,Complex.cosh_mul_I,Complex.sinh_mul_I,
    ← Complex.ofReal_cosh,← Complex.ofReal_cos,← Complex.ofReal_sinh,← Complex.ofReal_sin]
  push_cast
  ring

theorem spectral_sinh_abs_le_cosh_horizontal_norm (t y : ℝ) :
    |Real.sinh t| ≤ ‖Complex.cosh ((t : ℂ)+(y : ℂ)*I)‖ := by
  have he : ‖Complex.cosh ((t : ℂ)+(y : ℂ)*I)‖^2 = Real.sinh t^2+Real.cos y^2 := by
    rw [← Complex.normSq_eq_norm_sq,spectral_cosh_horizontal,Complex.normSq_apply]
    simp only [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_mul,zero_add,add_zero,sub_zero]
    linear_combination (Real.cos y)^2*(Real.cosh_sq_sub_sinh_sq t)+
      (Real.sinh t)^2*(Real.sin_sq_add_cos_sq y)
  apply (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp
  rw [sq_abs,he]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem spectral_exp_abs_le_cosh_horizontal_norm (t y : ℝ) :
    Real.exp |t| ≤ 2*(1+‖Complex.cosh ((t : ℂ)+(y : ℂ)*I)‖) := by
  have hs : Real.sinh |t| = |Real.sinh t| := by
    by_cases ht : 0 ≤ t
    · rw [abs_of_nonneg ht,abs_of_nonneg (Real.sinh_nonneg_iff.mpr ht)]
    · have ht' : t < 0 := lt_of_not_ge ht
      rw [abs_of_neg ht',Real.sinh_neg,abs_of_nonpos (Real.sinh_nonpos_iff.mpr ht'.le)]
  have he : Real.exp (-|t|) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg _))
  have hf : Real.exp |t| = 2*Real.sinh |t|+Real.exp (-|t|) := by rw [Real.sinh_eq]; ring
  rw [hf,hs]
  linarith [spectral_sinh_abs_le_cosh_horizontal_norm t y]

theorem spectralCompactLaplace_cosh_contour_bound (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ici (0 : ℝ))
    (ν : ℂ) (hν : |ν.re| ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t y : ℝ, 0 ≤ y → y ≤ Real.pi/2 →
      ‖Complex.exp (ν*((t : ℂ)+(y : ℂ)*I))*
        spectralCompactLaplace g (Complex.cosh ((t : ℂ)+(y : ℂ)*I))‖ ≤
        C*SourcePhysical.sourceContourHeightWeight t := by
  let M := (2 : ℝ)^3*((∫ x : ℝ, ‖g x‖)+(∫ x : ℝ, ‖iteratedDeriv 3 g x‖))
  have hM : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg (by norm_num) (add_nonneg (integral_nonneg fun _ => norm_nonneg _)
      (integral_nonneg fun _ => norm_nonneg _))
  let E := Real.exp (|ν.im| *(Real.pi/2))
  refine ⟨8*M*E,by positivity,?_⟩
  intro t y hy0 hy1
  let z : ℂ := (t : ℂ)+(y : ℂ)*I
  let T := Real.exp |t|
  have hT : 0 < T := Real.exp_pos _
  have hRe : 0 ≤ (Complex.cosh z).re := by
    rw [show Complex.cosh z = ((Real.cosh t*Real.cos y : ℝ) : ℂ)+
      ((Real.sinh t*Real.sin y : ℝ) : ℂ)*I from spectral_cosh_horizontal t y]
    simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,I_re,I_im,
      mul_zero,zero_mul,sub_self,add_zero]
    exact mul_nonneg (Real.cosh_pos t).le
      (Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos],hy1⟩)
  have hL : ‖spectralCompactLaplace g (Complex.cosh z)‖ ≤ M/(1+‖Complex.cosh z‖)^3 := by
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [one_mul,mul_one,one_pow,mul_comm,M] using
      spectralCompactLaplace_scaled_norm_le g hg hc hp 3 (b:=1) zero_le_one hRe
  have hscale : T/2 ≤ 1+‖Complex.cosh z‖ := by
    dsimp [T,z]
    linarith [spectral_exp_abs_le_cosh_horizontal_norm t y]
  have hdecay : ‖spectralCompactLaplace g (Complex.cosh z)‖ ≤ 8*M/T^3 := by
    apply hL.trans
    calc
      _ ≤ M/(T/2)^3 := div_le_div_of_nonneg_left hM (pow_pos (half_pos hT) _)
        (pow_le_pow_left₀ (half_pos hT).le hscale _)
      _ = _ := by rw [div_pow]; ring
  have hre : ν.re*t ≤ |t| := by
    calc
      _ ≤ |ν.re*t| := le_abs_self _
      _ = |ν.re| * |t| := abs_mul _ _
      _ ≤ _ := mul_le_of_le_one_left (abs_nonneg _) hν
  have him : -(ν.im*y) ≤ |ν.im| *(Real.pi/2) := by
    calc
      _ ≤ |ν.im*y| := neg_le_abs _
      _ = |ν.im| *y := by rw [abs_mul,abs_of_nonneg hy0]
      _ ≤ _ := mul_le_mul_of_nonneg_left hy1 (abs_nonneg _)
  have hE' : ‖Complex.exp (ν*z)‖ ≤ T*E := by
    rw [Complex.norm_exp]
    dsimp [T,E]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    simp only [z,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,Complex.ofReal_re,
      Complex.ofReal_im,I_re,I_im,mul_zero,mul_one,zero_mul,sub_zero,zero_sub,add_zero,zero_add]
    linarith
  have hT2 : 1+t^2 ≤ T^2 := by
    have ht : 1+|t| ≤ T := by simpa only [add_comm] using Real.add_one_le_exp |t|
    exact (by nlinarith [sq_abs t,abs_nonneg t] : 1+t^2 ≤ (1+|t|)^2).trans
      (pow_le_pow_left₀ (by positivity) ht 2)
  change ‖Complex.exp (ν*z)*spectralCompactLaplace g (Complex.cosh z)‖ ≤ _
  rw [norm_mul]
  calc
    _ ≤ (T*E)*(8*M/T^3) := mul_le_mul hE' hdecay (norm_nonneg _) (by positivity)
    _ = (8*M*E)/T^2 := by field_simp [hT.ne'] <;> ring
    _ ≤ (8*M*E)/(1+t^2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hT2
    _ = _ := by rw [SourcePhysical.sourceContourHeightWeight,div_eq_mul_inv]

theorem spectralCompactLaplace_cosh_shift (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ici (0 : ℝ))
    (ν : ℂ) (hν : |ν.re| ≤ 1) :
    Integrable (fun t : ℝ => Complex.exp (ν*(t : ℂ))*
      spectralCompactLaplace g ((Real.sinh t : ℂ)*I)) ∧
    (∫ t : ℝ, Complex.exp (ν*(t : ℂ))*spectralCompactLaplace g (Real.cosh t : ℂ)) =
      Complex.exp (ν*((Real.pi/2 : ℝ) : ℂ)*I)*
        (∫ t : ℝ, Complex.exp (ν*(t : ℂ))*
          spectralCompactLaplace g ((Real.sinh t : ℂ)*I)) := by
  let F : ℂ → ℂ := fun z => Complex.exp (ν*z)*spectralCompactLaplace g (Complex.cosh z)
  let B := Real.pi/2
  let c := Complex.exp (ν*(B : ℂ)*I)
  let G : ℝ → ℂ := fun t => Complex.exp (ν*(t : ℂ))*spectralCompactLaplace g ((Real.sinh t : ℂ)*I)
  have hF : Differentiable ℂ F := by
    dsimp [F]
    exact (by fun_prop : Differentiable ℂ (fun z : ℂ => Complex.exp (ν*z))).mul
      ((spectralCompactLaplace_entire g hg.continuous hc).comp (by fun_prop))
  obtain ⟨C,hC,hbound⟩ := spectralCompactLaplace_cosh_contour_bound g hg hc hp ν hν
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hTop (t : ℝ) : F ((t : ℂ)+(B : ℂ)*I) = c*G t := by
    have hcosh : Complex.cosh ((t : ℂ)+(B : ℂ)*I) = (Real.sinh t : ℂ)*I := by
      rw [spectral_cosh_horizontal]
      simp [B,Real.cos_pi_div_two,Real.sin_pi_div_two]
    dsimp only [F,c,G]
    rw [hcosh,mul_add,Complex.exp_add]
    simp only [mul_assoc]
    ring
  have hI : Integrable (fun t : ℝ => F ((t : ℂ)+(B : ℂ)*I)) := by
    apply (SourcePhysical.sourceContourHeightWeight_integrable.const_mul C).mono'
      (hF.continuous.comp
        (show Continuous (fun t : ℝ => (t : ℂ)+(B : ℂ)*I) from by fun_prop)).aestronglyMeasurable
    exact ae_of_all _ fun t => hbound t B hB le_rfl
  have hc0 : c ≠ 0 := Complex.exp_ne_zero _
  have hG : Integrable G := by
    apply (hI.const_mul c⁻¹).congr
    filter_upwards with t
    rw [hTop,← mul_assoc,inv_mul_cancel₀ hc0,one_mul]
  refine ⟨hG,?_⟩
  have he := spectral_horizontal_integral_eq_of_heightWeight F hB
    (fun z _ _ => hF z) (fun t y hy0 hyB => hbound t y hy0 hyB)
  simp only [hTop,integral_const_mul] at he
  simpa only [F,← Complex.ofReal_cosh,c,G,B] using he

end
end ArtinMatthews
