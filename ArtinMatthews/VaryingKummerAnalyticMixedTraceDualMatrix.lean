module

public import ArtinMatthews.VaryingKummerAnalyticMixedTraceDualLattice
public import ArtinMatthews.VaryingKummerAnalyticMixedTheta


set_option backward.privateInPublic true
@[expose] public section

/-! Integer enumeration of the adjoint matrix is exactly enumeration of the
trace-dual fractional ideal. The two integral bases need not have the same
index type. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open Module NumberField NumberField.mixedEmbedding
open ArtinMatthews.ReusedTheta
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

theorem mixedIdealMatrix_single (i : MixedIdealIndex K I) :
    mixedIdealMatrix K I (EuclideanSpace.single i 1) =
      (mixedIdealOrthonormalBasis K I).repr (mixedIdealEuclideanBasis K I i) := by
  change (mixedIdealOrthonormalBasis K I).repr
    ((mixedIdealEuclideanBasis K I).equivFun.symm (Pi.single i 1)) = _
  rw [Basis.equivFun_symm_apply]
  simp

/-- A vector in the matrix dual, expressed in the original mixed Euclidean space. -/
def mixedDualMatrixVector (z : MixedIdealIndex K I → ℤ) : euclidean.mixedSpace K :=
  (mixedIdealOrthonormalBasis K I).repr.symm
    (adjointEquiv (mixedIdealMatrix K I).symm (euclideanInteger z))

theorem mixedDualMatrixVector_pair (i : MixedIdealIndex K I)
    (z : MixedIdealIndex K I → ℤ) :
    inner ℝ (mixedIdealEuclideanBasis K I i) (mixedDualMatrixVector K I z) =
      (z i : ℝ) := by
  rw [← (mixedIdealOrthonormalBasis K I).repr.inner_map_map]
  simp only [mixedDualMatrixVector, LinearIsometryEquiv.apply_symm_apply]
  change inner ℝ ((mixedIdealOrthonormalBasis K I).repr (mixedIdealEuclideanBasis K I i))
    ((mixedIdealMatrix K I).symm.toContinuousLinearMap.adjoint (euclideanInteger z)) = _
  rw [ContinuousLinearMap.adjoint_inner_right,
    ← mixedIdealMatrix_single K I i, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply, EuclideanSpace.inner_single_left]
  simp [euclideanInteger, integerVector]

theorem mixedDualMatrixVector_mem (z : MixedIdealIndex K I → ℤ) :
    mixedDualMatrixVector K I z ∈ mixedEuclideanDualLattice K I := by
  rw [mem_mixedEuclideanDualLattice]
  intro a
  let c := (fractionalIdealBasis K I.1).equivFun a
  refine ⟨∑ i, c i * z i, ?_⟩
  have ha := mixedIdealEuclideanBasis_integer_apply K I c
  simp only [c, LinearEquiv.symm_apply_apply] at ha
  rw [← ha, Basis.equivFun_symm_apply, sum_inner]
  simp only [inner_smul_left, RCLike.conj_to_real, mixedDualMatrixVector_pair,
    Int.cast_sum, Int.cast_mul]
  rfl

/-- The integer coordinates of the adjoint matrix enumerate the whole Euclidean dual lattice. -/
def mixedDualIntegerToLattice : (MixedIdealIndex K I → ℤ) ≃ mixedEuclideanDualLattice K I :=
  Equiv.ofBijective (fun z => ⟨mixedDualMatrixVector K I z, mixedDualMatrixVector_mem K I z⟩)
    ⟨by
      intro z w h
      ext i
      have hi := congrArg (fun v : mixedEuclideanDualLattice K I =>
        inner ℝ (mixedIdealEuclideanBasis K I i) (v : euclidean.mixedSpace K)) h
      simpa only [mixedDualMatrixVector_pair, Int.cast_inj] using hi,
    by
      intro v
      have hv := (mem_mixedEuclideanDualLattice K I v).mp v.property
      choose z hz using fun i : MixedIdealIndex K I => hv (fractionalIdealBasis K I.1 i)
      refine ⟨z, Subtype.ext ?_⟩
      apply InnerProductSpace.ext_inner_left_basis (mixedIdealEuclideanBasis K I)
      intro i
      rw [mixedDualMatrixVector_pair, mixedIdealEuclideanBasis_apply, hz]⟩

/-- The normalized embedding enumerates exactly the same Euclidean dual lattice. -/
def mixedTraceIdealToDualLattice : (mixedTraceDualIdeal K I).1 ≃ mixedEuclideanDualLattice K I :=
  Equiv.ofBijective (fun b => ⟨mixedTraceTransform K (mixedFieldEmbedding K (b : K)),
    (mixedTraceTransform_mem_dual_iff K I b).mpr b.property⟩)
    ⟨by
      intro a b h
      apply Subtype.ext
      apply (mixedEmbedding K).injective
      apply (euclidean.toMixed K).symm.injective
      apply (mixedTraceTransform K).injective
      exact congrArg Subtype.val h,
    by
      intro v
      obtain ⟨b, hb⟩ := (mem_mixedEuclideanDualLattice_iff_traceDual K I v).mp v.property
      exact ⟨b, Subtype.ext hb⟩⟩

/-- Explicitly constructed equivalence between the two summation domains. -/
def mixedDualIntegerEquiv : (MixedIdealIndex K I → ℤ) ≃ (mixedTraceDualIdeal K I).1 :=
  (mixedDualIntegerToLattice K I).trans (mixedTraceIdealToDualLattice K I).symm

end
end ArtinMatthews.VaryingKummerAnalytic
