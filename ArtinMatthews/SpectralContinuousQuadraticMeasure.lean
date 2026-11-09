module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real


set_option backward.privateInPublic true
@[expose] public section

/-! The scalar spectral measure of a normal bounded operator is obtained
from its actual continuous functional calculus and Riesz–Markov. -/
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace CompactlySupported
namespace ArtinMatthews

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def spectralCFCRealLift {X : Type*} [TopologicalSpace X] (f : C(X,ℝ)) : C(X,ℂ) :=
  ⟨fun x => (f x:ℂ),Complex.continuous_ofReal.comp f.continuous⟩

theorem spectralCFCRealLift_apply {X : Type*} [TopologicalSpace X] (f : C(X,ℝ)) (x : X) :
    spectralCFCRealLift f x=(f x:ℂ) := rfl

theorem spectralCFCRealLift_add {X : Type*} [TopologicalSpace X] (f g : C(X,ℝ)) :
    spectralCFCRealLift (f+g)=spectralCFCRealLift f+spectralCFCRealLift g := by
  ext x
  simp only [spectralCFCRealLift_apply,ContinuousMap.add_apply,Complex.ofReal_add]

theorem spectralCFCRealLift_smul {X : Type*} [TopologicalSpace X] (a : ℝ) (f : C(X,ℝ)) :
    spectralCFCRealLift (a • f)=(a:ℂ) • spectralCFCRealLift f := by
  ext x
  simp only [spectralCFCRealLift_apply,ContinuousMap.smul_apply,smul_eq_mul,Complex.ofReal_mul]

theorem spectralCFCRealLift_star {X : Type*} [TopologicalSpace X] (f : C(X,ℝ)) :
    star (spectralCFCRealLift f)=spectralCFCRealLift f := by
  ext x
  change (starRingEnd ℂ) (f x:ℂ)=(f x:ℂ)
  exact Complex.conj_ofReal _

def spectralQuadraticRealLinear (T : H →L[ℂ] H) (hT : IsStarNormal T) (u : H) :
    C_c(spectrum ℂ T,ℝ) →ₗ[ℝ] ℝ where
  toFun f := (inner ℂ u ((cfcHom hT (spectralCFCRealLift f.toContinuousMap)) u)).re
  map_add' f g := by
    change (inner ℂ u ((cfcHom hT (spectralCFCRealLift (f.toContinuousMap+g.toContinuousMap))) u)).re=_
    rw [spectralCFCRealLift_add,map_add,add_apply,inner_add_right,Complex.add_re]
  map_smul' a f := by
    change (inner ℂ u ((cfcHom hT (spectralCFCRealLift (a • f.toContinuousMap))) u)).re=_
    rw [spectralCFCRealLift_smul,map_smul,smul_apply,inner_smul_right,
      Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    rfl

theorem spectralQuadraticRealLinear_nonneg (T : H →L[ℂ] H) (hT : IsStarNormal T) (u : H)
    (f : C_c(spectrum ℂ T,ℝ)) (hf : 0≤f) : 0≤spectralQuadraticRealLinear T hT u f := by
  let q : C(spectrum ℂ T,ℂ) :=
    ⟨fun x => (Real.sqrt (f x):ℂ),Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp f.continuous)⟩
  have hq : spectralCFCRealLift f.toContinuousMap=star q*q := by
    ext x
    change (f x:ℂ)=(starRingEnd ℂ) (Real.sqrt (f x):ℂ)*(Real.sqrt (f x):ℂ)
    rw [Complex.conj_ofReal,← Complex.ofReal_mul,Real.mul_self_sqrt (hf x)]
  change 0≤(inner ℂ u ((cfcHom hT (spectralCFCRealLift f.toContinuousMap)) u)).re
  rw [hq,map_mul,map_star,ContinuousLinearMap.star_eq_adjoint,mul_apply_eq_comp,
    ContinuousLinearMap.adjoint_inner_right]
  exact (sq_nonneg ‖(cfcHom hT q) u‖).trans_eq (inner_self_eq_norm_sq (𝕜:=ℂ) _).symm

def spectralQuadraticPositiveMap (T : H →L[ℂ] H) (hT : IsStarNormal T) (u : H) :
    C_c(spectrum ℂ T,ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀ (spectralQuadraticRealLinear T hT u) (spectralQuadraticRealLinear_nonneg T hT u)

def spectralQuadraticMeasure (T : H →L[ℂ] H) (hT : IsStarNormal T) (u : H) :
    Measure (spectrum ℂ T) :=
  RealRMK.rieszMeasure (spectralQuadraticPositiveMap T hT u)

instance spectralQuadraticMeasure_isFinite (T : H →L[ℂ] H) (hT : IsStarNormal T) (u : H) :
    IsFiniteMeasure (spectralQuadraticMeasure T hT u) := by
  unfold spectralQuadraticMeasure
  infer_instance

theorem spectralQuadraticMeasure_integral_real (T : H →L[ℂ] H) (hT : IsStarNormal T) (u : H)
    (f : C(spectrum ℂ T,ℝ)) :
    (∫ x, f x ∂spectralQuadraticMeasure T hT u)=
      (inner ℂ u ((cfcHom hT (spectralCFCRealLift f)) u)).re :=
  RealRMK.integral_rieszMeasure (spectralQuadraticPositiveMap T hT u) ⟨f,HasCompactSupport.of_compactSpace f⟩

end ArtinMatthews
