module

public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint


set_option backward.privateInPublic true
@[expose] public section

/-! The actual canonical fractional-ideal lattice for arbitrary number fields.
No totally-real hypothesis is used. The Euclidean metric here is the standard
real/complex product metric; trace-normalized metrics and the unit average
needed for Dedekind zeta are subsequent, separate constructions. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open Module NumberField NumberField.mixedEmbedding
open scoped NumberField nonZeroDivisors Classical

noncomputable section

variable (K : Type*) [Field K] [NumberField K]
variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

abbrev MixedIdealIndex := Module.Free.ChooseBasisIndex ℤ I

/-- Coordinates of a fractional-ideal integral basis and standard mixed
coordinates have the same real dimension. -/
def mixedIdealIndexEquiv : MixedIdealIndex K I ≃ mixedEmbedding.index K :=
  Fintype.equivOfCardEq ((Module.finrank_eq_card_basis
    (mixedEmbedding.fractionalIdealLatticeBasis K I)).symm.trans
    (Module.finrank_eq_card_basis (mixedEmbedding.stdBasis K)))

/-- The canonical fractional-ideal basis transported to the Euclidean mixed space. -/
def mixedIdealEuclideanBasis :
    Basis (MixedIdealIndex K I) ℝ (euclidean.mixedSpace K) :=
  (mixedEmbedding.fractionalIdealLatticeBasis K I).map (euclidean.toMixed K).symm.toLinearEquiv

/-- A norm-preserving coordinate system, indexed by the ideal basis. -/
def mixedIdealOrthonormalBasis :
    OrthonormalBasis (MixedIdealIndex K I) ℝ (euclidean.mixedSpace K) :=
  (euclidean.stdOrthonormalBasis K).reindex (mixedIdealIndexEquiv K I).symm

/-- The concrete invertible matrix whose integer images are the canonical
fractional ideal in orthonormal coordinates. -/
def mixedIdealMatrix : EuclideanSpace ℝ (MixedIdealIndex K I) ≃L[ℝ]
    EuclideanSpace ℝ (MixedIdealIndex K I) :=
  ((EuclideanSpace.equiv (MixedIdealIndex K I) ℝ).trans
    (mixedIdealEuclideanBasis K I).equivFunL.symm).trans
    (mixedIdealOrthonormalBasis K I).repr.toContinuousLinearEquiv

/-- Actual canonical embedding with the standard mixed Euclidean metric. -/
def mixedIdealEmbedding (a : I.1) : euclidean.mixedSpace K :=
  (euclidean.toMixed K).symm (mixedEmbedding K (a : K))

@[simp] theorem mixedIdealEuclideanBasis_apply (j : MixedIdealIndex K I) :
    mixedIdealEuclideanBasis K I j =
      mixedIdealEmbedding K I (fractionalIdealBasis K I.1 j) := by
  simp [mixedIdealEuclideanBasis, mixedIdealEmbedding, basisOfFractionalIdeal_apply]

/-- Changing integral coordinates really enumerates elements of the ideal. -/
theorem mixedIdealEuclideanBasis_integer_apply (z : MixedIdealIndex K I → ℤ) :
    (mixedIdealEuclideanBasis K I).equivFun.symm (fun j => (z j : ℝ)) =
      mixedIdealEmbedding K I ((fractionalIdealBasis K I.1).equivFun.symm z) := by
  simp only [Basis.equivFun_symm_apply, mixedIdealEuclideanBasis_apply,
    mixedIdealEmbedding, Submodule.coe_sum, Submodule.coe_smul_of_tower,
    map_sum, map_zsmul]
  simp only [Int.cast_smul_eq_zsmul]

/-- The matrix and the actual fractional ideal have identical Gaussian radii. -/
theorem mixedIdealMatrix_integer_norm (z : MixedIdealIndex K I → ℤ) :
    ‖mixedIdealMatrix K I (WithLp.toLp 2 (fun j => (z j : ℝ)))‖ =
      ‖mixedIdealEmbedding K I ((fractionalIdealBasis K I.1).equivFun.symm z)‖ := by
  change ‖(mixedIdealOrthonormalBasis K I).repr
    ((mixedIdealEuclideanBasis K I).equivFun.symm (fun j => (z j : ℝ)))‖ = _
  rw [LinearIsometryEquiv.norm_map, mixedIdealEuclideanBasis_integer_apply]

/-- The real dimension is the degree of the number field, including complex places. -/
theorem mixedIdealIndex_card : Fintype.card (MixedIdealIndex K I) = Module.finrank ℚ K := by
  rw [← Module.finrank_eq_card_basis (mixedIdealEuclideanBasis K I), euclidean.finrank]

end
end ArtinMatthews.VaryingKummerAnalytic
