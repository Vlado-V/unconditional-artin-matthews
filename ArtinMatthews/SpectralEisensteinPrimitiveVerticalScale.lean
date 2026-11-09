module

public import ArtinMatthews.SpectralEisensteinPrimitiveProfilePairing
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper


set_option backward.privateInPublic true
@[expose] public section

/-! The exact primitive height change in the completed pairing. The true
width factor cancels the Jacobian of y=w*t and its hyperbolic density. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal
namespace ArtinMatthews

theorem spectralCuspVerticalMeasure_primitive_normalization {w Y : ℝ} (hw : 0<w) (hY : 0<Y)
    (F : ℝ → ℂ) :
    w • (∫ y, F (y/w) ∂cuspVerticalMeasure Y)=
      ∫ t in Ioi (Y/w), ((t^2:ℝ)⁻¹) • F t := by
  have hd : (∫ y, F (y/w) ∂cuspVerticalMeasure Y)=
      ∫ y in Ioi Y, ((y^2:ℝ)⁻¹) • F (y/w) := by
    simpa only [cuspHorizontalMeasure_univ,ENNReal.ofReal_one,one_smul,zpow_neg,zpow_ofNat] using
      cuspVerticalL2_integral_complex_density zero_lt_one hY (fun y => F (y/w))
  let G (t : ℝ) := ((t^2:ℝ)⁻¹) • F t
  have hFact : (∫ y in Ioi Y, ((y^2:ℝ)⁻¹) • F (y/w))=
      ∫ y in Ioi Y, ((w^2:ℝ)⁻¹) • G (y/w) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    change Y<y at hy
    change ((y^2:ℝ)⁻¹) • F (y/w)=((w^2:ℝ)⁻¹) • (((y/w)^2:ℝ)⁻¹) • F (y/w)
    rw [smul_smul]
    congr 1
    field_simp [hw.ne',(hY.trans hy).ne']
  have hChange : (∫ y in Ioi Y, G (y/w))=w • ∫ t in Ioi (Y/w),G t := by
    simpa only [div_eq_mul_inv,inv_inv] using integral_comp_mul_right_Ioi G Y (inv_pos.mpr hw)
  rw [hd,hFact,integral_smul,hChange,smul_smul,smul_smul,
    show w*(w^2)⁻¹*w=1 by field_simp [hw.ne'],one_smul]

end ArtinMatthews
