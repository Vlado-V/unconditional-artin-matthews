module

public import ArtinMatthews.SourceComplexLatticePoisson
public import ArtinMatthews.VaryingKummerAnalyticMixedTraceDualTheta


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.VaryingKummerAnalytic
open MeasureTheory Module NumberField NumberField.InfinitePlace
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]

def sourceComplexFieldEmbedding (a : K) : {v : InfinitePlace K // IsComplex v} → ℂ :=
  fun v => v.val.embedding a

def sourceMixedComplexEquiv :
    mixedEmbedding.mixedSpace K ≃L[ℝ] ({v : InfinitePlace K // IsComplex v} → ℂ) :=
  ({ toFun := Prod.snd
     invFun := fun x => (0, x)
     left_inv := by
       intro x
       have := source_complex_real_places_empty K
       exact Prod.ext (Subsingleton.elim _ _) rfl
     right_inv := fun _ => rfl
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } :
       mixedEmbedding.mixedSpace K ≃ₗ[ℝ] ({v : InfinitePlace K // IsComplex v} → ℂ)).toContinuousLinearEquiv

def sourceEuclideanComplexEquiv :
    mixedEmbedding.euclidean.mixedSpace K ≃L[ℝ] ({v : InfinitePlace K // IsComplex v} → ℂ) :=
  (mixedEmbedding.euclidean.toMixed K).trans (sourceMixedComplexEquiv K)

theorem sourceEuclideanComplexEquiv_fieldEmbedding (a : K) :
    sourceEuclideanComplexEquiv K (mixedFieldEmbedding K a) = sourceComplexFieldEmbedding K a := by
  simp only [sourceEuclideanComplexEquiv, mixedFieldEmbedding,
    ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.apply_symm_apply]
  rfl

theorem sourceComplexTraceForm_field (a b : K) :
    sourceComplexTraceForm (sourceComplexFieldEmbedding K a) (sourceComplexFieldEmbedding K b) =
      (Algebra.trace ℚ K (a * b) : ℝ) := by
  have := source_complex_real_places_empty K
  rw [trace_eq_mixed_sum, sourceComplexTraceForm_apply]
  simp only [sourceComplexFieldEmbedding, map_mul, Finset.univ_eq_empty,
    Finset.sum_empty, zero_add]

variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

def sourceIdealComplexBasis :
    Basis (MixedIdealIndex K I) ℝ ({v : InfinitePlace K // IsComplex v} → ℂ) :=
  (mixedIdealEuclideanBasis K I).map (sourceEuclideanComplexEquiv K).toLinearEquiv

theorem sourceIdealComplexBasis_apply (i : MixedIdealIndex K I) :
    sourceIdealComplexBasis K I i =
      sourceComplexFieldEmbedding K ((fractionalIdealBasis K I.1 i : I.1) : K) := by
  rw [sourceIdealComplexBasis, Basis.map_apply, mixedIdealEuclideanBasis_apply]
  exact sourceEuclideanComplexEquiv_fieldEmbedding K _

theorem sourceIdealComplexBasis_integer (z : MixedIdealIndex K I → ℤ) :
    (sourceIdealComplexBasis K I).equivFunL.symm (fun i => (z i : ℝ)) =
      sourceComplexFieldEmbedding K (((fractionalIdealBasis K I.1).equivFun.symm z : I.1) : K) := by
  calc
    _ = sourceEuclideanComplexEquiv K
        ((mixedIdealEuclideanBasis K I).equivFun.symm (fun i => (z i : ℝ))) := by
      change (sourceIdealComplexBasis K I).equivFun.symm (fun i => (z i : ℝ)) = _
      simp only [sourceIdealComplexBasis, Basis.equivFun_symm_apply, Basis.map_apply,
        map_sum, map_smul, ContinuousLinearEquiv.coe_toLinearEquiv]
    _ = _ := by
      rw [mixedIdealEuclideanBasis_integer_apply]
      exact sourceEuclideanComplexEquiv_fieldEmbedding K _

theorem sourceIdealComplexBasis_dual_integer (z : MixedIdealIndex K I → ℤ) :
    (sourceComplexDualCoordinates (sourceIdealComplexBasis K I)).symm (fun i => (z i : ℝ)) =
      sourceComplexFieldEmbedding K (mixedDualIntegerEquiv K I z : K) := by
  apply (sourceComplexDualCoordinates (sourceIdealComplexBasis K I)).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  funext i
  rw [sourceComplexDualCoordinates,
    OAI.RepresentationTheory.Weil.AdelicSplitting.LatticeDualCoordinates.LocalAnalysis.latticeDualCoordinates_apply,
    sourceIdealComplexBasis_apply, sourceComplexTraceForm_field, mul_comm]
  have h := mixedDualMatrixVector_pair K I i z
  rw [← mixedDualIntegerEquiv_embedding, mixedIdealEuclideanBasis_apply] at h
  change inner ℝ (mixedFieldEmbedding K ((fractionalIdealBasis K I.1 i : I.1) : K)) _ = _ at h
  rw [mixedTraceTransform_inner_eq_trace] at h
  exact h.symm

end
end ArtinMatthews.VaryingKummerAnalytic
