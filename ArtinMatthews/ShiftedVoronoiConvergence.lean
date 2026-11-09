module

public import ArtinMatthews.ShiftedVoronoiReflection
public import Mathlib.NumberTheory.ModularForms.LFunction


set_option backward.privateInPublic true
@[expose] public section

/-!
# Convergence of the Mellin transform at a rational cusp

A rational horizontal translate of a cusp form is again a cusp form on an
arithmetic subgroup.  Mathlib's strong functional-equation theorem therefore
proves convergence of its imaginary-axis Mellin integral for every parameter.
Identifying that axis with the original form's rational vertical line gives
the convergence required by the reflected Mellin identity.
-/

noncomputable section

open Complex UpperHalfPlane Matrix GeneralLinearGroup MeasureTheory Set
open ConjAct Pointwise
open scoped MatrixGroups

namespace ArtinMatthews

private theorem rationalTranslate_isArithmetic
    (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.IsArithmetic] (x : ℚ) :
    (toConjAct (upperRightHom (x : ℝ))⁻¹ • Γ).IsArithmetic := by
  have hmap : (upperRightHom x).map (Rat.castHom ℝ) = upperRightHom (x : ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [GeneralLinearGroup.map_apply]
  simpa only [GeneralLinearGroup.map_inv, hmap] using
    Subgroup.IsArithmetic.conj Γ (upperRightHom x)⁻¹

private theorem cuspForm_translate_upperRight_apply
    {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (f : CuspForm Γ k) (x : ℝ) (z : ℍ) :
    CuspForm.translate f (upperRightHom x) z = f (x +ᵥ z) := by
  rw [CuspForm.coe_translate, ModularForm.slash_def]
  have hsmul : upperRightHom x • z = x +ᵥ z := by
    ext
    simp [σ, num, denom, coe_vadd, UpperHalfPlane.coe_smul, add_comm]
  simp only [hsmul]
  simp [σ, denom, GeneralLinearGroup.val_det_apply]

private theorem translated_axis_eq_vertical
    {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (f : CuspForm Γ k)
    (x y : ℝ) (hy : 0 < y) :
    CuspForm.translate f (upperRightHom x) (ofComplex (Complex.I * y)) =
      cuspVerticalRestriction f x y := by
  rw [cuspForm_translate_upperRight_apply]
  simp only [cuspVerticalRestriction, dite_eq_left hy]
  congr 1
  ext
  simp [coe_vadd, ofComplex_apply_of_im_pos, hy, cuspVerticalPoint, mul_comm]

/-- The vertical Mellin integral of a positive-weight cusp form converges at
every complex parameter above every rational point. -/
theorem cuspVerticalRestriction_mellinConvergent
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ}
    (hk : 0 < k) (f : CuspForm Γ k) (x : ℚ) (s : ℂ) :
    MellinConvergent (cuspVerticalRestriction f (x : ℝ)) s := by
  let := rationalTranslate_isArithmetic Γ x
  have hc := ((CuspForm.isStrongFEPair hk
    (CuspForm.translate f (upperRightHom (x : ℝ)))).hasMellin s).1
  apply hc.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact congrArg (fun z : ℂ ↦ (y : ℂ) ^ (s - 1) • z)
    (translated_axis_eq_vertical f x y hy)

/-- The Mellin transform above a rational point is entire. -/
theorem cuspVerticalRestriction_mellin_differentiable
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ}
    (hk : 0 < k) (f : CuspForm Γ k) (x : ℚ) :
    Differentiable ℂ (mellin (cuspVerticalRestriction f (x : ℝ))) := by
  let := rationalTranslate_isArithmetic Γ x
  have hd := CuspForm.differentiable_Λ hk
    (CuspForm.translate f (upperRightHom (x : ℝ)))
  have he : ModularForm.Λ hk (CuspForm.translate f (upperRightHom (x : ℝ))) =
      mellin (cuspVerticalRestriction f (x : ℝ)) := by
    rw [CuspForm.Λ_eq_mellin]
    funext s
    unfold mellin
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    exact congrArg (fun z : ℂ ↦ (y : ℂ) ^ (s - 1) • z)
      (translated_axis_eq_vertical f x y hy)
  exact he ▸ hd

end ArtinMatthews
