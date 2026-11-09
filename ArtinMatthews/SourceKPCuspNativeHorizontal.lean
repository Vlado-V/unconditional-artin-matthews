module

public import ArtinMatthews.SourceKPCuspTraceFunctional
public import ArtinMatthews.SourceHyperbolicProductCalculus


set_option backward.privateInPublic true
@[expose] public section

/-! The actual Minkowski horizontal directions are the native Cartesian
horizontal directions in the product of upper half spaces. -/
namespace ArtinMatthews
open NumberField Module OAI.CubicEisenstein SourceHyperbolicGreen
open scoped NumberField Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
local notation "E" => mixedEmbedding.mixedSpace K
local notation "P" => ProductSpace (InfinitePlace K)

def sourceKPCuspComplexProjection (v : InfinitePlace K) : E →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj ⟨v,IsTotallyComplex.isComplex v⟩).comp (ContinuousLinearMap.snd ℝ _ _)

theorem sourceKPCuspComplexProjection_apply (v : InfinitePlace K) (x : E) :
    sourceKPCuspComplexProjection K v x = x.2 ⟨v,IsTotallyComplex.isComplex v⟩ := rfl

def sourceKPCuspProductHorizontalCLM : E →L[ℝ] P :=
  ContinuousLinearMap.pi fun v =>
    (Complex.reCLM.comp (sourceKPCuspComplexProjection K v)).smulRight (euclideanCoordinateVector 0) +
    (Complex.imCLM.comp (sourceKPCuspComplexProjection K v)).smulRight (euclideanCoordinateVector 1)

theorem sourceKPCuspProductHorizontalCLM_apply (x : E) (v : InfinitePlace K) :
    sourceKPCuspProductHorizontalCLM K x v =
      (sourceKPCuspComplexProjection K v x).re • euclideanCoordinateVector 0 +
      (sourceKPCuspComplexProjection K v x).im • euclideanCoordinateVector 1 := rfl

theorem sourceKPCuspProductHorizontalCLM_re (x : E) (v : InfinitePlace K) :
    sourceKPCuspProductHorizontalCLM K x v 0 = (sourceKPCuspComplexProjection K v x).re := by
  simp [sourceKPCuspProductHorizontalCLM_apply,euclideanCoordinateVector]

theorem sourceKPCuspProductHorizontalCLM_im (x : E) (v : InfinitePlace K) :
    sourceKPCuspProductHorizontalCLM K x v 1 = (sourceKPCuspComplexProjection K v x).im := by
  simp [sourceKPCuspProductHorizontalCLM_apply,euclideanCoordinateVector]

theorem sourceKPCuspProductHorizontalCLM_height (x : E) (v : InfinitePlace K) :
    sourceKPCuspProductHorizontalCLM K x v 2 = 0 := by
  simp [sourceKPCuspProductHorizontalCLM_apply,euclideanCoordinateVector]

theorem sourceKPCuspProductHorizontalCLM_direction (v : InfinitePlace K) (k : Fin 2) :
    sourceKPCuspProductHorizontalCLM K (sourceKPCuspHorizontalDirection K v k) =
      productDirection v k.castSucc := by
  funext w
  rw [sourceKPCuspProductHorizontalCLM_apply,productDirection]
  by_cases hw : w = v
  · subst w
    rw [Pi.single_eq_same]
    fin_cases k
    · rw [sourceKPCuspComplexProjection_apply,← mixedEmbedding.stdBasis_apply_isComplex_fst,
        ← mixedEmbedding.stdBasis_apply_isComplex_snd]
      simp [sourceKPCuspHorizontalDirection, Basis.repr_self,Finsupp.single_apply]
    · rw [sourceKPCuspComplexProjection_apply,← mixedEmbedding.stdBasis_apply_isComplex_fst,
        ← mixedEmbedding.stdBasis_apply_isComplex_snd]
      simp [sourceKPCuspHorizontalDirection, Basis.repr_self,Finsupp.single_apply]
  · rw [Pi.single_eq_of_ne hw,sourceKPCuspComplexProjection_apply,
      ← mixedEmbedding.stdBasis_apply_isComplex_fst,← mixedEmbedding.stdBasis_apply_isComplex_snd]
    simp [sourceKPCuspHorizontalDirection,Basis.repr_self,Finsupp.single_apply,hw,Ne.symm hw]

end
end ArtinMatthews
