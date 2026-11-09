module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Complex.Norm


set_option backward.privateInPublic true
@[expose] public section

/-! Orthogonal changes of real coordinates preserve the complex gradient square. -/
namespace ArtinMatthews.SourceArchJacquet
open scoped BigOperators
noncomputable section

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma sourceArch_orthonormal_gradient_square (b : OrthonormalBasis ι ℝ E)
    (A : E →L[ℝ] ℂ) (e : E ≃ₗᵢ[ℝ] E) :
    (∑ i, ‖A (e (b i))‖ ^ 2) = ∑ i, ‖A (b i)‖ ^ 2 := by
  have h (c : OrthonormalBasis ι ℝ E) :
      (∑ i, ‖A (c i)‖ ^ 2) =
        ‖Complex.reCLM.comp A‖ ^ 2 + ‖Complex.imCLM.comp A‖ ^ 2 := by
    simp_rw [Complex.sq_norm, Complex.normSq_apply, ← sq]
    rw [Finset.sum_add_distrib]
    change (∑ i, (Complex.reCLM.comp A) (c i) ^ 2) +
      (∑ i, (Complex.imCLM.comp A) (c i) ^ 2) = _
    rw [← c.norm_dual (Complex.reCLM.comp A), ← c.norm_dual (Complex.imCLM.comp A)]
  exact (h (b.map e)).trans (h b).symm

lemma sourceArch_scaled_orthonormal_gradient_square (b : OrthonormalBasis ι ℝ E)
    (A : E →L[ℝ] ℂ) (e : E ≃ₗᵢ[ℝ] E) (r : ℝ) :
    (∑ i, ‖A ((r • e.toContinuousLinearEquiv.toContinuousLinearMap) (b i))‖ ^ 2) =
      r ^ 2 * ∑ i, ‖A (b i)‖ ^ 2 := by
  simp_rw [smul_apply, map_smul, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs]
  rw [← Finset.mul_sum]
  exact congrArg (fun s : ℝ => r ^ 2 * s) (sourceArch_orthonormal_gradient_square b A e)

omit [Fintype ι] in
lemma sourceArch_scaled_linearIsometry [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) (r : ℝ) (hr : 0 < r)
    (hA : ∀ x, ‖A x‖ = r * ‖x‖) :
    ∃ e : E ≃ₗᵢ[ℝ] E, A = r • e.toContinuousLinearEquiv.toContinuousLinearMap := by
  let f : E →ₗᵢ[ℝ] E :=
    { toLinearMap := r⁻¹ • A.toLinearMap
      norm_map' := by
        intro x
        change ‖r⁻¹ • A x‖ = ‖x‖
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, hA x,
          inv_mul_cancel_left₀ hr.ne'] }
  refine ⟨f.toLinearIsometryEquiv rfl, ?_⟩
  ext x
  change A x = r • (r⁻¹ • A x)
  rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]

end
end ArtinMatthews.SourceArchJacquet
