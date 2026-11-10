module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! The orthogonal decomposition at a real Fredholm center of a bounded
self-adjoint Hilbert-space pencil. -/

namespace ArtinMatthews.HilbertResolvent

open scoped InnerProductSpace
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def pencil (T : E →L[ℂ] E) (z : ℂ) : E →L[ℂ] E := 1 - (z + 1) • T

def nullSpace (T : E →L[ℂ] E) (center : ℝ) : Submodule ℂ E :=
  (pencil T (center : ℂ)).ker

def regularSpace (T : E →L[ℂ] E) (center : ℝ) : Submodule ℂ E :=
  (nullSpace T center)ᗮ

theorem centerScalar_ne_zero {center : ℝ} (hne : center + 1 ≠ 0) :
    (center : ℂ) + 1 ≠ 0 := by
  exact_mod_cast hne

theorem apply_of_mem_null (T : E →L[ℂ] E) (center : ℝ) (hne : center + 1 ≠ 0)
    {x : E} (hx : x ∈ nullSpace T center) :
    T x = (((center : ℂ) + 1)⁻¹ : ℂ) • x := by
  change x - ((center : ℂ) + 1) • T x = 0 at hx
  have he : ((center : ℂ) + 1) • T x = x := (sub_eq_zero.mp hx).symm
  calc
    T x = (((center : ℂ) + 1)⁻¹ : ℂ) • (((center : ℂ) + 1) • T x) := by
      rw [smul_smul, inv_mul_cancel₀ (centerScalar_ne_zero hne), one_smul]
    _ = _ := congrArg (fun u : E => (((center : ℂ) + 1)⁻¹ : ℂ) • u) he

theorem pencil_apply_of_mem_null (T : E →L[ℂ] E) (center : ℝ) (hne : center + 1 ≠ 0)
    (z : ℂ) {x : E} (hx : x ∈ nullSpace T center) :
    pencil T z x = (((center : ℂ) - z) / ((center : ℂ) + 1)) • x := by
  change x - (z + 1) • T x = _
  rw [apply_of_mem_null T center hne hx, smul_smul]
  calc
    _ = (1 - (z + 1) * ((center : ℂ) + 1)⁻¹) • x := by rw [sub_smul, one_smul]
    _ = _ := by
      congr 1
      field_simp [centerScalar_ne_zero hne] <;> ring

variable [CompleteSpace E]

instance nullSpaceComplete (T : E →L[ℂ] E) (center : ℝ) :
    CompleteSpace (nullSpace T center) :=
  (pencil T (center : ℂ)).isClosed_ker.completeSpace_coe

instance regularSpaceComplete (T : E →L[ℂ] E) (center : ℝ) :
    CompleteSpace (regularSpace T center) :=
  (nullSpace T center).isClosed_orthogonal.completeSpace_coe

theorem nullSpace_isCompl_regularSpace (T : E →L[ℂ] E) (center : ℝ) :
    IsCompl (nullSpace T center) (regularSpace T center) :=
  (nullSpace T center).isCompl_orthogonal

theorem nullSpace_finiteDimensional (T : E →L[ℂ] E) (center : ℝ)
    (hF : (pencil T (center : ℂ)).IsFredholm) : FiniteDimensional ℂ (nullSpace T center) :=
  hF.finite_ker

theorem preserves_regularSpace (T : E →L[ℂ] E) (hT : IsSelfAdjoint T)
    (center : ℝ) (hne : center + 1 ≠ 0) {x : E} (hx : x ∈ regularSpace T center) :
    T x ∈ regularSpace T center := by
  apply ((nullSpace T center).mem_orthogonal _).mpr
  intro v hv
  have he : inner ℂ v (T x) = inner ℂ (T v) x := by
    simpa only [ContinuousLinearMap.coe_coe] using (hT.isSymmetric v x).symm
  rw [he, apply_of_mem_null T center hne hv, inner_smul_left,
    (nullSpace T center).inner_right_of_mem_orthogonal hv hx, mul_zero]

theorem pencil_center_selfAdjoint (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (center : ℝ) :
    IsSelfAdjoint (pencil T (center : ℂ)) := by
  simp [pencil, isSelfAdjoint_iff, hT.star_eq]

theorem pencil_center_range (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (center : ℝ)
    (hF : (pencil T (center : ℂ)).IsFredholm) :
    (pencil T (center : ℂ)).range = regularSpace T center := by
  have h := (pencil T (center : ℂ)).orthogonal_ker
  rw [(pencil_center_selfAdjoint T hT center).adjoint_eq,
    hF.isClosed_range.submodule_topologicalClosure_eq] at h
  exact h.symm

end
end ArtinMatthews.HilbertResolvent
