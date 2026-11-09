module

public import ArtinMatthews.SpectralCuspTrueWidth
public import ArtinMatthews.SpectralCuspBruhatKernel


set_option backward.privateInPublic true
@[expose] public section

/-! The actual determinant-one scaling by the genuine cusp width. -/

noncomputable section
open Matrix Set MeasureTheory
open scoped MatrixGroups

namespace ArtinMatthews

def cuspWidthDilation (w : ℝ) (hw : 0 < w) : SL(2, ℝ) :=
  ⟨!![Real.sqrt w,0;0,(Real.sqrt w)⁻¹],by
    have hs := (Real.sqrt_pos.mpr hw).ne'
    simp [Matrix.det_fin_two,hs]⟩

theorem cuspWidthDilation_coe_smul (w : ℝ) (hw : 0 < w) (z : UpperHalfPlane) :
    ((cuspWidthDilation w hw • z : UpperHalfPlane) : ℂ) = (w : ℂ) * z := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [cuspWidthDilation,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one,Matrix.of_apply,Algebra.algebraMap_self_apply,Complex.ofReal_zero,
    zero_mul,add_zero,zero_add,Complex.ofReal_inv]
  rw [div_inv_eq_mul]
  have hs : ((Real.sqrt w : ℝ) : ℂ)^2 = (w : ℂ) := by exact_mod_cast Real.sq_sqrt hw.le
  linear_combination (z : ℂ)*hs

theorem cuspWidthDilation_re_smul (w : ℝ) (hw : 0 < w) (z : UpperHalfPlane) :
    (cuspWidthDilation w hw • z).re = w*z.re := by
  have h := congrArg Complex.re (cuspWidthDilation_coe_smul w hw z)
  simpa using h

theorem cuspWidthDilation_im_smul (w : ℝ) (hw : 0 < w) (z : UpperHalfPlane) :
    (cuspWidthDilation w hw • z).im = w*z.im := by
  have h := congrArg Complex.im (cuspWidthDilation_coe_smul w hw z)
  simpa using h

set_option backward.isDefEq.respectTransparency false in
theorem cuspWidthDilation_translation (w : ℝ) (hw : 0 < w) (x : ℝ) :
    cuspWidthDilation w hw * realTranslation x =
      realTranslation (w*x) * cuspWidthDilation w hw := by
  have hs := (Real.sqrt_pos.mpr hw).ne'
  have hsq := Real.sq_sqrt hw.le
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [cuspWidthDilation,realTranslation,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply,Fin.sum_univ_two]
  field_simp [hs]
  linear_combination x*hsq

theorem cuspWidthDilation_conjugate_translation (w : ℝ) (hw : 0 < w) (x : ℝ) :
    cuspWidthDilation w hw * realTranslation x * (cuspWidthDilation w hw)⁻¹ =
      realTranslation (w*x) := by
  rw [cuspWidthDilation_translation,mul_assoc,mul_inv_cancel,mul_one]

theorem atkinRealMap_integerTranslation (k : ℤ) :
    atkinRealMap (integerTranslation k) = realTranslation (k : ℝ) := by
  ext i j
  change ((integerTranslation k) i j : ℝ) = (realTranslation (k : ℝ)) i j
  fin_cases i <;> fin_cases j <;> simp [integerTranslation,realTranslation]

def gamma0TrueCuspScaling (N : ℕ) [NeZero N] (r : SL(2, ℤ)) : SL(2, ℝ) :=
  (atkinRealMap r)⁻¹ * cuspWidthDilation (gamma0CuspTrueWidth N r : ℝ)
    (by exact_mod_cast gamma0CuspTrueWidth_pos N r)

theorem gamma0TrueCuspScaling_conjugate_translation (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (x : ℝ) :
    gamma0TrueCuspScaling N r * realTranslation x * (gamma0TrueCuspScaling N r)⁻¹ =
      (atkinRealMap r)⁻¹ * realTranslation ((gamma0CuspTrueWidth N r : ℝ)*x) * atkinRealMap r := by
  have hw : 0 < (gamma0CuspTrueWidth N r : ℝ) := by exact_mod_cast gamma0CuspTrueWidth_pos N r
  unfold gamma0TrueCuspScaling
  calc
    _ = (atkinRealMap r)⁻¹ *
        (cuspWidthDilation (gamma0CuspTrueWidth N r : ℝ) hw * realTranslation x *
          (cuspWidthDilation (gamma0CuspTrueWidth N r : ℝ) hw)⁻¹) * atkinRealMap r := by group
    _ = _ := by rw [cuspWidthDilation_conjugate_translation]

theorem gamma0TrueCuspScaling_integer_period (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (k : ℤ) :
    ∃ γ : CongruenceSubgroup.Gamma0 N,
      atkinRealMap γ.val = gamma0TrueCuspScaling N r * realTranslation (k : ℝ) *
        (gamma0TrueCuspScaling N r)⁻¹ := by
  let a : SL(2, ℤ) := r⁻¹ * integerTranslation ((gamma0CuspTrueWidth N r : ℤ)*k) * r
  have ha : a ∈ CongruenceSubgroup.Gamma0 N :=
    (gamma0CuspTrueWidth_translation_iff N r _).mpr (dvd_mul_right _ _)
  refine ⟨⟨a,ha⟩,?_⟩
  rw [gamma0TrueCuspScaling_conjugate_translation]
  simp only [a,map_mul,map_inv,atkinRealMap_integerTranslation,Int.cast_mul,Int.cast_natCast]

end ArtinMatthews
