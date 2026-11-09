module

public import ArtinMatthews.SpectralContinuousQuadraticMeasure
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap


set_option backward.privateInPublic true
@[expose] public section

/-! Exact continuous functional-calculus integrals and the scalar
measure norm identity for the actual operator state. -/
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace ENNReal
namespace ArtinMatthews

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem spectralCFCRealLift_inner_eq_real (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (u : H) (f : C(spectrum ℂ T,ℝ)) :
    inner ℂ u ((cfcHom hT (spectralCFCRealLift f)) u)=
      (((inner ℂ u ((cfcHom hT (spectralCFCRealLift f)) u)).re:ℝ):ℂ) := by
  let A := cfcHom hT (spectralCFCRealLift f)
  have hstar : star A=A := by
    change star (cfcHom hT (spectralCFCRealLift f))=cfcHom hT (spectralCFCRealLift f)
    rw [← map_star,spectralCFCRealLift_star]
  have he : (starRingEnd ℂ) (inner ℂ u (A u))=inner ℂ u (A u) := by
    calc
      _ = inner ℂ (A u) u := inner_conj_symm (𝕜:=ℂ) (A u) u
      _ = inner ℂ ((star A) u) u := congrArg (fun F : H →L[ℂ] H => inner ℂ (F u) u) hstar.symm
      _ = _ := ContinuousLinearMap.adjoint_inner_left A u u
  have hi : (inner ℂ u (A u)).im=0 := by
    have h := congrArg Complex.im he
    rw [Complex.conj_im] at h
    linarith
  change inner ℂ u (A u)=((inner ℂ u (A u)).re:ℂ)
  exact Complex.ext (by simp) (by simpa only [Complex.ofReal_im] using hi)

theorem spectralQuadraticMeasure_integral_complex (T : H →L[ℂ] H) (hT : IsStarNormal T) (u : H)
    (f : C(spectrum ℂ T,ℂ)) :
    (∫ x,f x ∂spectralQuadraticMeasure T hT u)=inner ℂ u ((cfcHom hT f) u) := by
  let μ := spectralQuadraticMeasure T hT u
  let a : C(spectrum ℂ T,ℝ) := ⟨fun x => (f x).re,Complex.continuous_re.comp f.continuous⟩
  let b : C(spectrum ℂ T,ℝ) := ⟨fun x => (f x).im,Complex.continuous_im.comp f.continuous⟩
  have hInt : Integrable f μ := f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have hdecomp : f=spectralCFCRealLift a+Complex.I • spectralCFCRealLift b := by
    ext x
    change f x=((f x).re:ℂ)+Complex.I*((f x).im:ℂ)
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]
  calc
    (∫ x,f x ∂μ) = ((∫ x,a x ∂μ : ℝ):ℂ)+((∫ x,b x ∂μ : ℝ):ℂ)*Complex.I :=
      (integral_re_add_im hInt).symm
    _ = inner ℂ u ((cfcHom hT (spectralCFCRealLift a)) u)+
        inner ℂ u ((cfcHom hT (spectralCFCRealLift b)) u)*Complex.I := by
      rw [spectralQuadraticMeasure_integral_real,spectralQuadraticMeasure_integral_real,
        ← spectralCFCRealLift_inner_eq_real T hT u a,← spectralCFCRealLift_inner_eq_real T hT u b]
    _ = _ := by
      rw [hdecomp,map_add,map_smul,add_apply,smul_apply,inner_add_right,inner_smul_right]
      ring

theorem spectralQuadraticMeasure_integral_norm_sq (T : H →L[ℂ] H) (hT : IsStarNormal T) (u : H)
    (f : C(spectrum ℂ T,ℂ)) :
    (∫ x,‖f x‖^2 ∂spectralQuadraticMeasure T hT u)=‖(cfcHom hT f) u‖^2 := by
  let q : C(spectrum ℂ T,ℝ) := ⟨fun x => ‖f x‖^2,f.continuous.norm.pow 2⟩
  have hq : spectralCFCRealLift q=star f*f := by
    ext x
    change ((‖f x‖^2:ℝ):ℂ)=(starRingEnd ℂ) (f x)*f x
    rw [Complex.ofReal_pow,← Complex.mul_conj',mul_comm]
  change (∫ x,q x ∂spectralQuadraticMeasure T hT u)=_
  rw [spectralQuadraticMeasure_integral_real,hq,map_mul,map_star,ContinuousLinearMap.star_eq_adjoint,
    mul_apply_eq_comp,ContinuousLinearMap.adjoint_inner_right]
  exact inner_self_eq_norm_sq (𝕜:=ℂ) _

theorem spectralQuadraticMeasure_univ (T : H →L[ℂ] H) (hT : IsStarNormal T) (u : H) :
    spectralQuadraticMeasure T hT u univ=ENNReal.ofReal (‖u‖^2) := by
  let μ := spectralQuadraticMeasure T hT u
  have h := spectralQuadraticMeasure_integral_norm_sq T hT u (1:C(spectrum ℂ T,ℂ))
  have hreal : μ.real univ=‖u‖^2 := by
    simpa [μ] using h
  rw [← hreal]
  exact (ENNReal.ofReal_toReal (measure_ne_top μ univ)).symm

end ArtinMatthews
