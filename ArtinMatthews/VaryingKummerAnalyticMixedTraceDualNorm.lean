module

public import ArtinMatthews.VaryingKummerAnalyticMixedTraceDual


set_option backward.privateInPublic true
@[expose] public section

/-! The actual archimedean radius on the trace-dual side of Poisson summation. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open Module NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem mixedTraceTransform_embedding_norm_sq (b : K) :
    ‖mixedTraceTransform K (mixedFieldEmbedding K b)‖ ^ 2 =
      ∑ w : InfinitePlace K, ((w.mult : ℝ) * w b) ^ 2 := by
  simp only [mixedFieldEmbedding, mixedTraceTransform,
    ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [WithLp.prod_norm_sq_eq_of_L2, EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq, InfinitePlace.sum_eq_sum_add_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro w _
    change ‖embedding_of_isReal w.property b‖ ^ 2 = _
    rw [InfinitePlace.norm_embedding_of_isReal]
    simp only [InfinitePlace.mult_isReal w, Nat.cast_one, one_mul]
  · apply Finset.sum_congr rfl
    intro w _
    change ‖(2 : ℂ) * star (w.1.embedding b)‖ ^ 2 = _
    simp [InfinitePlace.norm_embedding_eq, InfinitePlace.mult_isComplex w]

end
end ArtinMatthews.VaryingKummerAnalytic
