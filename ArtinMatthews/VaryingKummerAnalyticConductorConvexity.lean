module

public import ArtinMatthews.VaryingKummerAnalyticPrimitiveStripGrowth
public import ArtinMatthews.VaryingKummerAnalyticPrimitiveLeftBoundary
public import ArtinMatthews.VaryingKummerAnalyticQuadraticStripMaximum


set_option backward.privateInPublic true
@[expose] public section

/-! Conductor-sensitive strip interpolation. The generic strip argument is
immediately applied to the actual primitive continuation and its proved
Euler, functional-equation, Gamma-ratio and growth estimates. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex Set
open scoped NumberField nonZeroDivisors Classical
noncomputable section

def conductorNormalized (f : ℂ → ℂ) (A : ℝ) (m : ℕ) (z : ℂ) : ℂ :=
  (A : ℂ)^(z-5/4)*f z/(z+2)^m

theorem conductorNormalized_boundary_bound {f : ℂ → ℂ} {A C a : ℝ} (hA : 0 < A)
    (hC : 0 ≤ C) (ha : -1 ≤ a) (m : ℕ) {z : ℂ} (hz : z.re=a)
    (hf : ‖f z‖ ≤ C*A^(5/4-a)*(|z.im|+2)^m) :
    ‖conductorNormalized f A m z‖ ≤ C*3^m := by
  have hn1 : 1 ≤ ‖z+2‖ := by
    apply (show (1 : ℝ) ≤ (z+2).re by simpa [hz] using (show 1 ≤ a+2 by linarith)).trans
    exact Complex.re_le_norm _
  have hn : 0 < ‖z+2‖ := lt_of_lt_of_le zero_lt_one hn1
  have ht : |z.im|+2 ≤ 3*‖z+2‖ := by
    have hi := Complex.abs_im_le_norm (z+2)
    norm_num [Complex.add_im] at hi
    linarith
  have hp : A^(a-5/4)*A^(5/4-a) = 1 := by
    rw [← Real.rpow_add hA,show a-5/4+(5/4-a)=0 by ring,Real.rpow_zero]
  rw [conductorNormalized,norm_div,norm_mul,norm_pow,
    Complex.norm_cpow_eq_rpow_re_of_pos hA]
  have hre : (z-5/4).re = a-5/4 := by rw [Complex.sub_re,hz]; norm_num
  rw [hre]
  apply (div_le_iff₀ (pow_pos hn m)).mpr
  calc
    _ ≤ A^(a-5/4)*(C*A^(5/4-a)*(|z.im|+2)^m) :=
      mul_le_mul_of_nonneg_left hf (Real.rpow_nonneg hA.le _)
    _ = C*(|z.im|+2)^m := by
      calc
        _ = (A^(a-5/4)*A^(5/4-a))*(C*(|z.im|+2)^m) := by ring
        _ = _ := by rw [hp,one_mul]
    _ ≤ C*(3*‖z+2‖)^m := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith [abs_nonneg z.im]) ht _) hC
    _ = _ := by rw [mul_pow]; ring

theorem conductor_strip_convexity {f : ℂ → ℂ} {A C : ℝ} (hA : 0 < A) (hC : 0 < C)
    (m : ℕ) (hf : Differentiable ℂ f)
    (hleft : ∀ t : ℝ, ‖f ((-1/4 : ℂ)+(t : ℂ)*I)‖ ≤ C*A^(3/2 : ℝ)*(|t|+2)^m)
    (hright : ∀ t : ℝ, ‖f ((5/4 : ℂ)+(t : ℂ)*I)‖ ≤ C*(|t|+2)^m)
    (hg : ∃ E D R : ℝ, 0 < E ∧ 0 < D ∧ ∀ σ : ℝ,
      -(1/4 : ℝ) ≤ σ → σ ≤ 5/4 → ∀ t : ℝ, R ≤ |t| →
      ‖f ((σ : ℂ)+(t : ℂ)*I)‖ ≤ E*Real.exp (D*(|t|+2)^2))
    {z : ℂ} (hza : -(1/4 : ℝ) ≤ z.re) (hzb : z.re ≤ 5/4) :
    ‖f z‖ ≤ (C*6^m)*A^(5/4-z.re)*(|z.im|+2)^m := by
  let Q := conductorNormalized f A m
  have hn (w : ℂ) (hw : -(1/4 : ℝ) ≤ w.re) : 1 ≤ ‖w+2‖ := by
    apply (show (1 : ℝ) ≤ (w+2).re by norm_num; linarith).trans
    exact Complex.re_le_norm _
  have hnz (w : ℂ) (hw : -(1/4 : ℝ) ≤ w.re) : w+2 ≠ 0 := by
    exact norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one (hn w hw))
  have hpow : Differentiable ℂ (fun w : ℂ => (A : ℂ)^(w-5/4)) :=
    (differentiable_id.sub_const _).const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hA.ne'))
  have hclosed : closure (Complex.re ⁻¹' Ioo (-(1/4 : ℝ)) (5/4)) ⊆
      {w : ℂ | -(1/4 : ℝ) ≤ w.re ∧ w.re ≤ 5/4} := by
    apply ((isClosed_le continuous_const Complex.continuous_re).inter
        (isClosed_le Complex.continuous_re continuous_const)).closure_subset_iff.mpr
    intro w hw
    exact ⟨hw.1.le,hw.2.le⟩
  have hdiff : DiffContOnCl ℂ Q (Complex.re ⁻¹' Ioo (-(1/4 : ℝ)) (5/4)) := by
    apply DifferentiableOn.diffContOnCl
    intro w hw
    exact (((hpow w).mul (hf w)).div ((differentiableAt_id.add_const 2).pow m)
      (pow_ne_zero _ (hnz w (hclosed hw).1))).differentiableWithinAt
  have hscale (w : ℂ) (hwa : -(1/4 : ℝ) ≤ w.re) (hwb : w.re ≤ 5/4) :
      ‖(A : ℂ)^(w-5/4)‖ ≤ Real.exp (2*|Real.log A|) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hA,Real.rpow_def_of_pos hA]
    apply Real.exp_le_exp.mpr
    have hh : |(w-5/4).re| ≤ 2 := by
      have he : (w-5/4).re = w.re-5/4 := by norm_num
      rw [he]
      exact abs_le.mpr ⟨by linarith,by linarith⟩
    calc
      Real.log A*(w-5/4).re ≤ |Real.log A*(w-5/4).re| := le_abs_self _
      _ = |Real.log A| * |(w-5/4).re| := abs_mul _ _
      _ ≤ |Real.log A| * 2 := mul_le_mul_of_nonneg_left hh (abs_nonneg _)
      _ = _ := by ring
  obtain ⟨E,D,R,hE,hD,hg⟩ := hg
  have hqgrowth (w : ℂ) (hwa : -(1/4 : ℝ) ≤ w.re) (hwb : w.re ≤ 5/4) (hR : R ≤ |w.im|) :
      ‖Q w‖ ≤ (Real.exp (2*|Real.log A|)*E)*Real.exp (D*(|w.im|+2)^2) := by
    have H := hg w.re hwa hwb w.im hR
    rw [Complex.re_add_im] at H
    change ‖conductorNormalized f A m w‖ ≤ _
    rw [conductorNormalized,norm_div,norm_mul,norm_pow]
    have hden : 1 ≤ ‖w+2‖^m := one_le_pow₀ (hn w hwa)
    calc
      _ ≤ ‖(A : ℂ)^(w-5/4)‖*‖f w‖ := div_le_self (by positivity) hden
      _ ≤ Real.exp (2*|Real.log A|)*(E*Real.exp (D*(|w.im|+2)^2)) :=
        mul_le_mul (hscale w hwa hwb) H (norm_nonneg _) (Real.exp_pos _).le
      _ = _ := by ring
  have hqb : ∀ w : ℂ, w.re=5/4 → ‖Q w‖ ≤ C*3^m := by
    intro w hw
    apply conductorNormalized_boundary_bound hA hC.le (by norm_num : (-1 : ℝ) ≤ 5/4) m hw
    have H := hright w.im
    have he : (5/4 : ℂ)+(w.im : ℂ)*I = w := by
      have he := Complex.re_add_im w
      rw [hw] at he
      norm_num at he
      exact he
    simpa only [he,sub_self,Real.rpow_zero,mul_one] using H
  have hqa : ∀ w : ℂ, w.re=-(1/4 : ℝ) → ‖Q w‖ ≤ C*3^m := by
    intro w hw
    apply conductorNormalized_boundary_bound (a := -(1/4 : ℝ)) hA hC.le (by norm_num) m hw
    have H := hleft w.im
    have he : (-1/4 : ℂ)+(w.im : ℂ)*I = w := by
      have he := Complex.re_add_im w
      rw [hw] at he
      norm_num at he
      simpa only [neg_div] using he
    rw [he] at H
    convert H using 1
    norm_num
  have HQ := norm_le_on_vertical_strip_of_quadratic_growth
    (by norm_num : -(1/4 : ℝ) < 5/4) (mul_pos (Real.exp_pos _) hE) hD.le hdiff hqgrowth hqa hqb hza hzb
  change ‖conductorNormalized f A m z‖ ≤ C*3^m at HQ
  rw [conductorNormalized,norm_div,norm_mul,norm_pow,Complex.norm_cpow_eq_rpow_re_of_pos hA] at HQ
  have Hclear := (div_le_iff₀ (pow_pos (lt_of_lt_of_le zero_lt_one (hn z hza)) m)).mp HQ
  have Hmul := mul_le_mul_of_nonneg_left Hclear (Real.rpow_nonneg hA.le (5/4-z.re))
  have hp : A^(5/4-z.re)*A^((z-5/4).re) = 1 := by
    rw [← Real.rpow_add hA]
    norm_num
  have hnorm : ‖z+2‖ ≤ 2*(|z.im|+2) := by
    have H := Complex.norm_le_abs_re_add_abs_im (z+2)
    norm_num [Complex.add_re,Complex.add_im] at H
    rw [abs_of_nonneg (by linarith : 0 ≤ z.re+2)] at H
    linarith [abs_nonneg z.im]
  calc
    ‖f z‖ = A^(5/4-z.re)*(A^((z-5/4).re)*‖f z‖) := by rw [← mul_assoc,hp,one_mul]
    _ ≤ A^(5/4-z.re)*(C*3^m*‖z+2‖^m) := Hmul
    _ ≤ A^(5/4-z.re)*(C*3^m*(2*(|z.im|+2))^m) := by
      gcongr
    _ = _ := by
      rw [mul_pow,show (6 : ℝ)=3*2 by norm_num,mul_pow]
      ring

theorem exists_primitiveContinued_conductor_convexity
    (K : Type*) [Field K] [NumberField K] :
    ∃ (C : ℝ) (m : ℕ), 0 < C ∧
      ∀ {M : Ideal (𝓞 K)} (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)
        (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
        (_hnp : ψ.IsNonprincipal) (z : ℂ), -(1/4 : ℝ) ≤ z.re → z.re ≤ 5/4 →
        ‖ψ.primitiveContinued hM hprim z‖ ≤ C*
          (mixedConductorScale K (integralIdealFractionalUnit M hM))^(5/4-z.re)*(|z.im|+2)^m := by
  obtain ⟨C,m,hC,hleft⟩ := exists_primitiveContinued_left_boundary_bound K
  let B := C+primitiveReciprocalBound K
  have hB : 0 < B := add_pos hC (primitiveReciprocalBound_pos K)
  refine ⟨B*6^m,m,mul_pos hB (by positivity),?_⟩
  intro M ψ hM hprim hnp z hza hzb
  apply conductor_strip_convexity (mixedConductorScale_pos K (integralIdealFractionalUnit M hM)) hB m
    (ψ.primitiveContinued_entire hM hprim) _ _
    (ψ.primitiveContinued_convexity_strip_growth hM hprim hnp) hza hzb
  · intro t
    apply (hleft ψ hM hprim hnp t).trans
    have hc : C ≤ B := le_add_of_nonneg_right (primitiveReciprocalBound_pos K).le
    have hp : 0 ≤ (mixedConductorScale K (integralIdealFractionalUnit M hM))^(3/2 : ℝ) *
        (|t|+2)^m := mul_nonneg (Real.rpow_nonneg (mixedConductorScale_pos K _).le _) (by positivity)
    convert mul_le_mul_of_nonneg_right hc hp using 1 <;> ring
  · intro t
    have H := ψ.primitiveContinued_norm_le_right hM hprim hnp
      (s := (5/4 : ℂ)+(t : ℂ)*I) (by norm_num)
    apply H.trans
    have hb : primitiveReciprocalBound K ≤ B := le_add_of_nonneg_left hC.le
    exact hb.trans (le_mul_of_one_le_right hB.le (one_le_pow₀ (by linarith [abs_nonneg t])))

end
end ArtinMatthews.VaryingKummerAnalytic
