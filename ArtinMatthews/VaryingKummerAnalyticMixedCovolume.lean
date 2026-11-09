module

public import ArtinMatthews.VaryingKummerAnalyticMixedLattice
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! The exact covolume of the canonical ideal lattice for mixed signature.
This retains the complex-place factor; no totally-real replacement is made. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open Module NumberField NumberField.mixedEmbedding
open scoped NumberField nonZeroDivisors Classical

noncomputable section

variable (K : Type*) [Field K] [NumberField K]
variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

/-- The image of the fractional ideal in the actual Euclidean mixed space. -/
def mixedIdealLattice : Submodule ℤ (euclidean.mixedSpace K) :=
  ZLattice.comap ℝ (mixedEmbedding.idealLattice K I) (euclidean.toMixed K).toLinearMap

instance : DiscreteTopology (mixedIdealLattice K I) := by
  unfold mixedIdealLattice
  infer_instance

instance : IsZLattice ℝ (mixedIdealLattice K I) := by
  unfold mixedIdealLattice
  infer_instance

/-- Membership in this lattice is literal ideal membership under the embedding. -/
theorem mem_mixedIdealLattice (x : euclidean.mixedSpace K) :
    x ∈ mixedIdealLattice K I ↔ ∃ a : I.1, mixedIdealEmbedding K I a = x := by
  change (euclidean.toMixed K) x ∈ mixedEmbedding.idealLattice K I ↔ _
  rw [mixedEmbedding.mem_idealLattice]
  constructor
  · rintro ⟨a, ha, he⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    dsimp [mixedIdealEmbedding]
    rw [he, ContinuousLinearEquiv.symm_apply_apply]
  · rintro ⟨a, ha⟩
    refine ⟨a, a.property, ?_⟩
    rw [← ha]
    exact (euclidean.toMixed K).apply_symm_apply _ |>.symm

/-- The literal ideal and the embedded lattice are linearly equivalent over the integers. -/
def mixedIdealToLattice : I.1 ≃ₗ[ℤ] mixedIdealLattice K I :=
  LinearEquiv.ofBijective
    { toFun := fun a => ⟨mixedIdealEmbedding K I a,
        (mem_mixedIdealLattice K I _).mpr ⟨a, rfl⟩⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        simp [mixedIdealEmbedding]
      map_smul' := by
        intro n a
        apply Subtype.ext
        change mixedIdealEmbedding K I (n • a) = n • mixedIdealEmbedding K I a
        simp only [mixedIdealEmbedding, Submodule.coe_smul_of_tower, map_zsmul] }
    ⟨by
      intro a b h
      apply Subtype.ext
      apply (mixedEmbedding K).injective
      apply (euclidean.toMixed K).symm.injective
      exact congrArg Subtype.val h,
      by
      intro x
      obtain ⟨a, ha⟩ := (mem_mixedIdealLattice K I x).mp x.property
      exact ⟨a, Subtype.ext ha⟩⟩

/-- The transported integral basis has exactly the canonical Euclidean basis vectors. -/
def mixedIdealIntegralBasis :
    Basis (MixedIdealIndex K I) ℤ (mixedIdealLattice K I) :=
  (fractionalIdealBasis K I.1).map (mixedIdealToLattice K I)

@[simp] theorem mixedIdealIntegralBasis_apply (j : MixedIdealIndex K I) :
    (mixedIdealIntegralBasis K I j : euclidean.mixedSpace K) =
      mixedIdealEuclideanBasis K I j := by
  rw [mixedIdealEuclideanBasis_apply]
  rfl

/-- The Gaussian matrix determinant is the determinant of the actual lattice basis
relative to orthonormal mixed coordinates. -/
theorem mixedIdealMatrix_det :
    LinearMap.det (mixedIdealMatrix K I).toLinearMap =
      (mixedIdealOrthonormalBasis K I).toBasis.det (mixedIdealEuclideanBasis K I) := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (MixedIdealIndex K I) ℝ).toBasis,
    Basis.det_apply]
  congr 1
  ext i j
  simp [LinearMap.toMatrix_apply, mixedIdealMatrix, Basis.toMatrix_apply,
    EuclideanSpace.basisFun_apply]
  change ((mixedIdealOrthonormalBasis K I).repr
    ((mixedIdealEuclideanBasis K I).equivFun.symm (Pi.single j 1))).ofLp i = _
  rw [Basis.equivFun_symm_apply]
  simp

/-- Exact dependence on norm, discriminant, and number of complex places. -/
theorem mixedIdealLattice_covolume :
    ZLattice.covolume (mixedIdealLattice K I) =
      (FractionalIdeal.absNorm I.1 : ℝ) *
        (2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K * Real.sqrt |(discr K : ℝ)| := by
  rw [mixedIdealLattice, ZLattice.covolume_comap _ _ _
    (euclidean.volumePreserving_toMixed K), mixedEmbedding.covolume_idealLattice]

end
end ArtinMatthews.VaryingKummerAnalytic
