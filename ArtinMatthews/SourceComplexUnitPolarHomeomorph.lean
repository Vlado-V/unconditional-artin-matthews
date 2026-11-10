module

public import ArtinMatthews.SourceComplexUnitPolar
public import Mathlib.MeasureTheory.Integral.Bochner.Basic


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open MeasureTheory
open scoped ENNReal
noncomputable section

theorem sourceComplexRadialUnit_continuous : Continuous sourceComplexRadialUnit := by
  apply Units.continuous_iff.mpr
  have h : Continuous (fun t : ℝ => (sourceComplexRadialUnit t : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_id.div_const 2))
  refine ⟨h, ?_⟩
  have hi : Continuous (fun t : ℝ => (sourceComplexRadialUnit t : ℂ)⁻¹) :=
    h.inv₀ (fun t => (sourceComplexRadialUnit t).ne_zero)
  simpa only [Units.val_inv_eq_inv_val] using hi

theorem sourceCircle_toUnits_continuous : Continuous Circle.toUnits := by
  apply Units.continuous_iff.mpr
  have h : Continuous (fun θ : Circle => (Circle.toUnits θ : ℂ)) := continuous_subtype_val
  have hi : Continuous (fun θ : Circle => (Circle.toUnits θ : ℂ)⁻¹) :=
    h.inv₀ (fun θ => (Circle.toUnits θ).ne_zero)
  exact ⟨h, by simpa only [Units.val_inv_eq_inv_val] using hi⟩

theorem sourceComplexUnitAngle_continuous : Continuous sourceComplexUnitAngle := by
  apply Continuous.subtype_mk
  have hc : Continuous (fun z : ℂˣ => (z : ℂ)) := Units.continuous_val
  exact hc.div (Complex.continuous_ofReal.comp hc.norm)
    (fun z => Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr z.ne_zero))

theorem sourceComplexUnitLogNorm_continuous : Continuous sourceComplexUnitLogNorm :=
  continuous_const.mul (Units.continuous_val.norm.log (fun z => norm_ne_zero_iff.mpr z.ne_zero))

def sourceComplexUnitPolarHomeomorph : Circle × Multiplicative ℝ ≃ₜ ℂˣ where
  toEquiv := sourceComplexUnitPolarMulEquiv.toEquiv
  continuous_toFun := by
    change Continuous (fun p : Circle × Multiplicative ℝ =>
      sourceComplexRadialUnit p.2.toAdd * Circle.toUnits p.1)
    exact (sourceComplexRadialUnit_continuous.comp continuous_snd).mul
      (sourceCircle_toUnits_continuous.comp continuous_fst)
  continuous_invFun := by
    change Continuous (fun z : ℂˣ => (sourceComplexUnitAngle z,
      Multiplicative.ofAdd (sourceComplexUnitLogNorm z)))
    exact sourceComplexUnitAngle_continuous.prodMk sourceComplexUnitLogNorm_continuous

end
end ArtinMatthews.SourcePhysical
