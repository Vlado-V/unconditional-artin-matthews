module

public import ArtinMatthews.VaryingKummerAnalyticMixedCovolume
public import Mathlib.RingTheory.DedekindDomain.Different


set_option backward.privateInPublic true
@[expose] public section

/-! The actual trace pairing in the Euclidean mixed embedding. Complex places
contribute twice their real trace, with conjugation in the Euclidean dual. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open Module NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped NumberField nonZeroDivisors Classical BigOperators

noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- The mixed Euclidean embedding of a field element. -/
def mixedFieldEmbedding (a : K) : euclidean.mixedSpace K :=
  (euclidean.toMixed K).symm (mixedEmbedding K a)

/-- Trace normalization: identity at real places and twice conjugation at
complex places. -/
def mixedTraceTransformRaw : mixedSpace K ≃ₗ[ℝ] mixedSpace K where
  toFun x := (x.1, fun w => 2 * star (x.2 w))
  invFun x := (x.1, fun w => (2 : ℂ)⁻¹ * star (x.2 w))
  left_inv x := by ext w <;> simp
  right_inv x := by ext w <;> simp
  map_add' x y := by ext w <;> simp [mul_add]
  map_smul' c x := by
    ext w <;> simp [Algebra.smul_def, mul_left_comm, mul_comm]

/-- Trace normalization transported to the standard Euclidean mixed metric. -/
def mixedTraceTransform : euclidean.mixedSpace K ≃L[ℝ] euclidean.mixedSpace K :=
  (euclidean.toMixed K).trans
    ((mixedTraceTransformRaw K).toContinuousLinearEquiv.trans (euclidean.toMixed K).symm)

theorem mixedTraceTransform_embedding_inner (a b : K) :
    inner ℝ (mixedFieldEmbedding K a)
      (mixedTraceTransform K (mixedFieldEmbedding K b)) =
      (∑ w : {w : InfinitePlace K // IsReal w},
        InfinitePlace.embedding_of_isReal w.property a *
          InfinitePlace.embedding_of_isReal w.property b) +
      ∑ w : {w : InfinitePlace K // IsComplex w},
        2 * (w.1.embedding (a * b)).re := by
  simp only [mixedFieldEmbedding, mixedTraceTransform,
    ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [WithLp.prod_inner_apply, PiLp.inner_apply, PiLp.inner_apply]
  congr 1
  · apply Finset.sum_congr rfl
    intro w _
    change (embedding_of_isReal w.property b) *
      (embedding_of_isReal w.property a) = _
    ring
  · apply Finset.sum_congr rfl
    intro w _
    change inner ℝ (w.1.embedding a) (2 * star (w.1.embedding b)) = _
    rw [real_inner_eq_re_inner (𝕜 := ℂ)]
    simp [RCLike.inner_apply, Complex.mul_re, map_mul]
    ring

theorem trace_eq_mixed_sum (a : K) :
    (Algebra.trace ℚ K a : ℝ) =
      (∑ w : {w : InfinitePlace K // IsReal w}, embedding_of_isReal w.property a) +
      ∑ w : {w : InfinitePlace K // IsComplex w}, 2 * (w.1.embedding a).re := by
  have h := trace_eq_sum_embeddings (K := ℚ) (L := K) (E := ℂ) (x := a)
  rw [← (RingHom.equivRatAlgHom K ℂ).sum_comp (fun σ => σ a)] at h
  change (algebraMap ℚ ℂ) (Algebra.trace ℚ K a) = ∑ σ : K →+* ℂ, σ a at h
  rw [← (indexEquiv K).sum_comp (fun σ => σ a), Fintype.sum_sum_type,
    Fintype.sum_prod_type] at h
  have hre := congrArg Complex.re h
  change ((Algebra.trace ℚ K a : ℚ) : ℂ).re = _ at hre
  simp only [Complex.ratCast_re, Complex.add_re, Complex.re_sum,
    indexEquiv_apply_isReal, indexEquiv_apply_isComplex_fst,
    indexEquiv_apply_isComplex_snd, Fin.sum_univ_two,
    ComplexEmbedding.conjugate_coe_eq, Complex.conj_re] at hre
  convert hre using 1
  congr 1
  apply Finset.sum_congr rfl
  intro w _
  ring

/-- The field trace is literally the mixed Euclidean pairing after the
complex-place normalization. -/
theorem mixedTraceTransform_inner_eq_trace (a b : K) :
    inner ℝ (mixedFieldEmbedding K a)
      (mixedTraceTransform K (mixedFieldEmbedding K b)) =
      (Algebra.trace ℚ K (a * b) : ℝ) := by
  rw [mixedTraceTransform_embedding_inner, trace_eq_mixed_sum]
  simp only [map_mul]

end
end ArtinMatthews.VaryingKummerAnalytic
