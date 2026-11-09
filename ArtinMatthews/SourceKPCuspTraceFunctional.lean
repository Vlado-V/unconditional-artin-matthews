module

public import ArtinMatthews.SourceKPCuspTraceFrequency


set_option backward.privateInPublic true
@[expose] public section

/-! The actual trace frequency as a real functional on the scaled Minkowski coordinates. -/
namespace ArtinMatthews
open NumberField Module Module.Free
open ArtinMatthews.VaryingKummerAnalytic
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K]
local notation "E" => mixedEmbedding.mixedSpace K

def sourceKPCuspTraceFunctional (ξ : K) : E →L[ℝ] ℝ :=
  (innerSL ℝ (mixedTraceTransform K (mixedFieldEmbedding K ξ))).comp
    (mixedEmbedding.euclidean.toMixed K).symm.toContinuousLinearMap

theorem sourceKPCuspTraceFunctional_embedding (ξ a : K) :
    sourceKPCuspTraceFunctional K ξ (mixedEmbedding K a) = (Algebra.trace ℚ K (a * ξ) : ℝ) := by
  change inner ℝ (mixedTraceTransform K (mixedFieldEmbedding K ξ)) (mixedFieldEmbedding K a) = _
  rw [real_inner_comm]
  exact mixedTraceTransform_inner_eq_trace K a ξ

variable (d : 𝓞 K) (hd : d ≠ 0)
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)

theorem sourceKPCuspTraceFunctional_basis (n : I → ℤ) (i : I) :
    sourceKPCuspTraceFunctional K (sourceKPCuspTraceFrequency K d n)
      (sourceKPCuspLatticeBasis K d hd i) = (n i : ℝ) := by
  rw [sourceKPCuspLatticeBasis_apply, sourceKPCuspTraceFunctional_embedding, mul_comm]
  exact sourceKPCuspTraceFrequency_pair K d hd n i

theorem sourceKPCuspTraceFunctional_coordinates (n : I → ℤ) (x : E) :
    sourceKPCuspTraceFunctional K (sourceKPCuspTraceFrequency K d n) x =
      ∑ i, sourceKPCuspCoordinates K d hd x i * (n i : ℝ) := by
  conv_lhs => rw [← (sourceKPCuspLatticeBasis K d hd).sum_repr x]
  simp only [map_sum, map_smul, sourceKPCuspTraceFunctional_basis, smul_eq_mul]
  rfl

omit hd in
 theorem sourceKPCuspTraceFunctional_stdBasis (ξ : K) (a : mixedEmbedding.index K) :
    sourceKPCuspTraceFunctional K ξ (mixedEmbedding.stdBasis K a) =
      (mixedEmbedding.stdBasis K).repr
        (mixedTraceTransformRaw K (mixedEmbedding K ξ)) a := by
  have he : (mixedEmbedding.euclidean.toMixed K).symm (mixedEmbedding.stdBasis K a) =
      mixedEmbedding.euclidean.stdOrthonormalBasis K a := by
    apply (mixedEmbedding.euclidean.toMixed K).injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    have h := congrArg (fun b : Basis (mixedEmbedding.index K) ℝ E => b a)
      (mixedEmbedding.euclidean.stdOrthonormalBasis_map_eq (K := K))
    exact h.symm
  change inner ℝ (mixedTraceTransform K (mixedFieldEmbedding K ξ))
    ((mixedEmbedding.euclidean.toMixed K).symm (mixedEmbedding.stdBasis K a)) = _
  rw [he, real_inner_comm, ← OrthonormalBasis.repr_apply_apply]
  rfl

variable [IsTotallyComplex K]

def sourceKPCuspHorizontalDirection (v : InfinitePlace K) (k : Fin 2) : E :=
  mixedEmbedding.stdBasis K (Sum.inr (⟨v, IsTotallyComplex.isComplex v⟩, k))

omit hd in
 theorem sourceKPCuspTraceFunctional_horizontal_zero (ξ : K) (v : InfinitePlace K) :
    sourceKPCuspTraceFunctional K ξ (sourceKPCuspHorizontalDirection K v 0) =
      2 * (v.embedding ξ).re := by
  rw [sourceKPCuspHorizontalDirection, sourceKPCuspTraceFunctional_stdBasis,
    mixedEmbedding.stdBasis_apply_isComplex_fst]
  simp [mixedTraceTransformRaw]

omit hd in
 theorem sourceKPCuspTraceFunctional_horizontal_one (ξ : K) (v : InfinitePlace K) :
    sourceKPCuspTraceFunctional K ξ (sourceKPCuspHorizontalDirection K v 1) =
      -(2 * (v.embedding ξ).im) := by
  rw [sourceKPCuspHorizontalDirection, sourceKPCuspTraceFunctional_stdBasis,
    mixedEmbedding.stdBasis_apply_isComplex_snd]
  simp [mixedTraceTransformRaw]

end
end ArtinMatthews
