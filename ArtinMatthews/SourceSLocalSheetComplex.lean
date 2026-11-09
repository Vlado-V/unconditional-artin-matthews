module

public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.MeasureTheory.Group.Circle
public import Mathlib.Topology.Algebra.Group.Units


set_option backward.privateInPublic true
@[expose] public section

/-! The angular coordinate and its positive-radius inverse in the actual
completion at a chosen complex infinite place. -/

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
noncomputable section

variable {K : Type} [Field K] {v : InfinitePlace K} (hv : IsComplex v)

theorem sourceSheetComplex_norm (z : v.Completion) :
    ‖ringEquivComplexOfIsComplex hv z‖ = ‖z‖ :=
  (isometryEquivComplexOfIsComplex hv).isometry.norm_map_of_map_zero
    (map_zero (ringEquivComplexOfIsComplex hv)) z

def sourceSheetComplexPhase (u : v.Completionˣ) : Circle :=
  ⟨ringEquivComplexOfIsComplex hv (u : v.Completion) / (‖(u : v.Completion)‖ : ℂ),
    mem_sphere_zero_iff_norm.mpr (by
      rw [norm_div, sourceSheetComplex_norm hv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.mpr u.ne_zero)])⟩

@[simp] theorem sourceSheetComplexPhase_coe (u : v.Completionˣ) :
    (sourceSheetComplexPhase hv u : ℂ) =
      ringEquivComplexOfIsComplex hv (u : v.Completion) / (‖(u : v.Completion)‖ : ℂ) := rfl

theorem sourceSheetComplexPhase_mul (u w : v.Completionˣ) :
    sourceSheetComplexPhase hv (u*w) = sourceSheetComplexPhase hv u * sourceSheetComplexPhase hv w := by
  apply Circle.ext
  simp only [sourceSheetComplexPhase_coe, Units.val_mul, map_mul, norm_mul, Complex.ofReal_mul,
    Circle.coe_mul]
  exact mul_div_mul_comm _ _ _ _

/-- Lift the unit circle and the specified positive radius to the chosen completion. -/
def sourceSheetComplexUnit (θ : Circle) (r : ℝ) (hr : 0 < r) : v.Completionˣ :=
  Units.map (ringEquivComplexOfIsComplex hv).symm.toMonoidHom
    (Circle.toUnits θ * Units.mk0 (r : ℂ) (Complex.ofReal_ne_zero.mpr hr.ne'))

@[simp] theorem sourceSheetComplexUnit_image (θ : Circle) (r : ℝ) (hr : 0 < r) :
    ringEquivComplexOfIsComplex hv (sourceSheetComplexUnit hv θ r hr : v.Completion) =
      (θ : ℂ) * (r : ℂ) := by
  change ringEquivComplexOfIsComplex hv
    ((ringEquivComplexOfIsComplex hv).symm ((θ : ℂ)*(r : ℂ))) = _
  exact (ringEquivComplexOfIsComplex hv).apply_symm_apply _

theorem sourceSheetComplexUnit_norm (θ : Circle) (r : ℝ) (hr : 0 < r) :
    ‖(sourceSheetComplexUnit hv θ r hr : v.Completion)‖ = r := by
  rw [← sourceSheetComplex_norm hv, sourceSheetComplexUnit_image, norm_mul, Circle.norm_coe,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, one_mul]

@[simp] theorem sourceSheetComplexUnit_phase (θ : Circle) (r : ℝ) (hr : 0 < r) :
    sourceSheetComplexPhase hv (sourceSheetComplexUnit hv θ r hr) = θ := by
  apply Circle.ext
  rw [sourceSheetComplexPhase_coe, sourceSheetComplexUnit_image, sourceSheetComplexUnit_norm,
    mul_div_cancel_right₀ _ (Complex.ofReal_ne_zero.mpr hr.ne')]

theorem sourceSheetComplexUnit_phase_norm (u : v.Completionˣ) :
    sourceSheetComplexUnit hv (sourceSheetComplexPhase hv u) ‖(u : v.Completion)‖
      (norm_pos_iff.mpr u.ne_zero) = u := by
  apply Units.ext
  apply (ringEquivComplexOfIsComplex hv).injective
  rw [sourceSheetComplexUnit_image, sourceSheetComplexPhase_coe,
    div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr u.ne_zero))]

theorem continuous_sourceSheetComplexPhase : Continuous (sourceSheetComplexPhase hv) := by
  refine Continuous.subtype_mk ?_ _
  have hz : Continuous (fun u : v.Completionˣ =>
      ringEquivComplexOfIsComplex hv (u : v.Completion)) :=
    (isometryEquivComplexOfIsComplex hv).continuous.comp Units.continuous_val
  have hr : Continuous (fun u : v.Completionˣ => (‖(u : v.Completion)‖ : ℂ)) :=
    Complex.continuous_ofReal.comp Units.continuous_val.norm
  exact hz.div hr (fun u => Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr u.ne_zero))

theorem continuous_sourceSheetComplexUnit {X : Type*} [TopologicalSpace X]
    {θ : X → Circle} {r : X → ℝ} (hθ : Continuous θ) (hr : Continuous r)
    (hp : ∀ x, 0 < r x) : Continuous (fun x => sourceSheetComplexUnit hv (θ x) (r x) (hp x)) := by
  have hθ' : Continuous (fun x => (θ x : ℂ)) := continuous_subtype_val.comp hθ
  have hval : Continuous (fun x => (sourceSheetComplexUnit hv (θ x) (r x) (hp x) : v.Completion)) :=
    (isometryEquivComplexOfIsComplex hv).symm.continuous.comp
      (hθ'.mul (Complex.continuous_ofReal.comp hr))
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  apply (hval.inv₀ (fun x => (sourceSheetComplexUnit hv (θ x) (r x) (hp x)).ne_zero)).congr
  intro x
  exact (Units.val_inv_eq_inv_val _).symm

end
end ArtinMatthews.SourcePhysical
