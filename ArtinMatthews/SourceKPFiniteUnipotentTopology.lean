module

public import ArtinMatthews.SourceKPFiniteSmoothSection
public import ArtinMatthews.SourceKPAdelicUpperProjection


set_option backward.privateInPublic true
@[expose] public section

/-! The actual finite upper-root curve approaches the identity in
the matrix group. Conjugation therefore enters the proved open
deep subgroup, while its full adelic projection stays exact. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Topology Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K]

theorem sourceKPFiniteUpperMatrix_continuous :
    Continuous (fun t : 𝔸ᶠ[K] => sourceKPUpperMatrix 𝔸ᶠ[K] t) := by
  have hv : Continuous (fun t : 𝔸ᶠ[K] =>
      (sourceKPUpperMatrix 𝔸ᶠ[K] t : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[K])) := by
    apply continuous_matrix
    intro i j
    fin_cases i <;> fin_cases j
    · change Continuous (fun _ : 𝔸ᶠ[K] => (1 : 𝔸ᶠ[K]))
      exact continuous_const
    · change Continuous (fun t : 𝔸ᶠ[K] => t)
      exact continuous_id
    · change Continuous (fun _ : 𝔸ᶠ[K] => (0 : 𝔸ᶠ[K]))
      exact continuous_const
    · change Continuous (fun _ : 𝔸ᶠ[K] => (1 : 𝔸ᶠ[K]))
      exact continuous_const
  have hi (t : 𝔸ᶠ[K]) : (sourceKPUpperMatrix 𝔸ᶠ[K] t)⁻¹ = sourceKPUpperMatrix 𝔸ᶠ[K] (-t) := by
    symm
    apply eq_inv_iff_mul_eq_one.mpr
    rw [← sourceKPUpperMatrix_add, neg_add_cancel, sourceKPUpperMatrix_zero]
  apply Units.continuous_iff.mpr
  refine ⟨hv, ?_⟩
  change Continuous (fun t : 𝔸ᶠ[K] =>
    ((sourceKPUpperMatrix 𝔸ᶠ[K] t)⁻¹ : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[K]))
  have he : (fun t : 𝔸ᶠ[K] =>
      ((sourceKPUpperMatrix 𝔸ᶠ[K] t)⁻¹ : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[K])) =
      (fun t : 𝔸ᶠ[K] => (sourceKPUpperMatrix 𝔸ᶠ[K] (-t) : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[K])) := by
    funext t
    exact congrArg (fun g : GL (Fin 2) 𝔸ᶠ[K] => (g : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[K])) (hi t)
  exact (congrArg Continuous he).mpr (hv.comp continuous_neg)

def sourceKPFiniteConjugateMatrix (a : GL (Fin 2) 𝔸ᶠ[K]) (t : 𝔸ᶠ[K]) : GL (Fin 2) 𝔸ᶠ[K] :=
  a⁻¹ * sourceKPUpperMatrix 𝔸ᶠ[K] t * a

theorem sourceKPFiniteConjugateMatrix_continuous (a : GL (Fin 2) 𝔸ᶠ[K]) :
    Continuous (sourceKPFiniteConjugateMatrix K a) :=
  (continuous_const.mul (sourceKPFiniteUpperMatrix_continuous K)).mul continuous_const

theorem sourceKPFiniteConjugateMatrix_zero (a : GL (Fin 2) 𝔸ᶠ[K]) :
    sourceKPFiniteConjugateMatrix K a 0 = 1 := by
  rw [sourceKPFiniteConjugateMatrix, sourceKPUpperMatrix_zero, mul_one, inv_mul_cancel]

theorem sourceKPFiniteConjugateMatrix_eventually_deep (a : GL (Fin 2) 𝔸ᶠ[K]) :
    ∀ᶠ t : 𝔸ᶠ[K] in nhds 0,
      sourceKPFiniteConjugateMatrix K a t ∈ sourceKPFiniteDeepMatrixGroup K := by
  have hU := (sourceKPFiniteDeepMatrixGroup_isOpen K).mem_nhds
    (sourceKPFiniteDeepMatrixGroup K).one_mem
  have ht : Filter.Tendsto (sourceKPFiniteConjugateMatrix K a) (nhds 0) (nhds 1) := by
    simpa only [sourceKPFiniteConjugateMatrix_zero] using
      (sourceKPFiniteConjugateMatrix_continuous K a).tendsto 0
  exact ht.eventually hU

theorem sourceKPFiniteUpperMatrix_embedding (t : 𝔸ᶠ[K]) :
    sourceKPFiniteMatrixEmbedding K (sourceKPUpperMatrix 𝔸ᶠ[K] t) =
      sourceKPUpperMatrix 𝔸[K] (0, t) := by
  apply GeneralLinearGroup.ext
  intro i j
  rw [sourceKPFiniteMatrixEmbedding_apply]
  fin_cases i <;> fin_cases j <;> simp [sourceKPUpperMatrix] <;> rfl

theorem sourceKPFiniteConjugateMatrix_embedding (a : GL (Fin 2) 𝔸[K]) (t : 𝔸ᶠ[K]) :
    sourceKPFiniteMatrixEmbedding K
      (sourceKPFiniteConjugateMatrix K (sourceKPGL2ProductEquiv K a).2 t) =
        a⁻¹ * sourceKPUpperMatrix 𝔸[K] (0, t) * a := by
  apply (sourceKPGL2ProductEquiv K).injective
  rw [sourceKPFiniteMatrixEmbedding_product, map_mul, map_mul, map_inv,
    ← sourceKPFiniteUpperMatrix_embedding, sourceKPFiniteMatrixEmbedding_product]
  apply Prod.ext
  · change (1 : GL (Fin 2) (InfiniteAdeleRing K)) =
      (sourceKPGL2ProductEquiv K a).1⁻¹ * 1 * (sourceKPGL2ProductEquiv K a).1
    group
  · rfl

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicFiniteConjugate_projection
    (g : SourceKPAdelicProjective K hζ) (a : GL (Fin 2) 𝔸[K])
    (ha : sourceKPAdelicProjectiveProjection K hζ g = ProjGenLinGroup.mk a) (t : 𝔸ᶠ[K]) :
    sourceKPAdelicProjectiveProjection K hζ (g⁻¹ * sourceKPAdelicUpperLift K hζ (0, t) * g) =
      ProjGenLinGroup.mk (sourceKPFiniteMatrixEmbedding K
        (sourceKPFiniteConjugateMatrix K (sourceKPGL2ProductEquiv K a).2 t)) := by
  have hN := sourceKPAdelicUpperLift_projection K hζ ((0, t) : 𝔸[K])
  calc
    _ = (ProjGenLinGroup.mk a)⁻¹ *
        sourceKPAdelicProjectiveProjection K hζ (sourceKPAdelicUpperLift K hζ (0, t)) *
          ProjGenLinGroup.mk a := by rw [map_mul, map_mul, map_inv, ha]
    _ = (ProjGenLinGroup.mk a)⁻¹ * ProjGenLinGroup.mk (sourceKPUpperMatrix 𝔸[K] (0, t)) *
          ProjGenLinGroup.mk a :=
      congrArg (fun b => (ProjGenLinGroup.mk a)⁻¹ * b * ProjGenLinGroup.mk a) hN
    _ = ProjGenLinGroup.mk (a⁻¹ * sourceKPUpperMatrix 𝔸[K] (0, t) * a) := by
      rw [map_mul, map_mul, map_inv]
    _ = _ := congrArg ProjGenLinGroup.mk (sourceKPFiniteConjugateMatrix_embedding K a t).symm

end
end ArtinMatthews
