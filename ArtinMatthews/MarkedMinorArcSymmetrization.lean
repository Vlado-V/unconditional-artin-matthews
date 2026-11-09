module

public import ArtinMatthews.MarkedMinorArcBlockOperator


set_option backward.privateInPublic true
@[expose] public section

/-! Actual independent left and right finite slot symmetrizations are L²
contractions. The two permutations need not be equal. -/
namespace ArtinMatthews
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

theorem markedMinorMatrix_submatrix_equiv_pair_norm_le {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (e f : κ ≃ ι) : ‖A.submatrix e f‖ ≤ ‖A‖ := by
  apply markedMinorMatrix_norm_le_of_energy _ (norm_nonneg _)
  intro g
  rw [Matrix.submatrix_mulVec_equiv A g e f]
  calc
    _ = ∑ i : ι, ‖(A *ᵥ (g ∘ f.symm)) i‖^2 :=
      e.sum_comp (fun i => ‖(A *ᵥ (g ∘ f.symm)) i‖^2)
    _ ≤ ‖A‖^2 * ∑ i : ι, ‖(g ∘ f.symm) i‖^2 :=
      markedMinorMatrix_energy_le_of_norm A (norm_nonneg _) le_rfl _
    _ = _ := by
      rw [← f.sum_comp (fun i => ‖(g ∘ f.symm) i‖^2)]
      simp only [Function.comp_apply,Equiv.symm_apply_apply]

/-- Independent finite row and column reindexings preserve the actual norm. -/
theorem markedMinorMatrix_submatrix_equiv_pair_norm {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (e f : κ ≃ ι) : ‖A.submatrix e f‖ = ‖A‖ := by
  apply le_antisymm (markedMinorMatrix_submatrix_equiv_pair_norm_le A e f)
  have hh := markedMinorMatrix_submatrix_equiv_pair_norm_le (A.submatrix e f) e.symm f.symm
  have he : (A.submatrix e f).submatrix e.symm f.symm=A := by ext i j; simp
  rwa [he] at hh

/-- Any actual probability average of independently reindexed kernels is
an L² contraction; this includes the source S*T*S slot averages. -/
theorem markedMinorMatrix_average_slotPairs_norm_le {ι J : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype J]
    (A : Matrix ι ι ℂ) (e f : J → Equiv.Perm ι) (weight : J → ℝ)
    (hw : ∀ j, 0 ≤ weight j) (hmass : ∑ j, weight j=1) :
    ‖∑ j, (weight j) • A.submatrix (e j) (f j)‖ ≤ ‖A‖ := by
  calc
    _ ≤ ∑ j, ‖(weight j) • A.submatrix (e j) (f j)‖ := norm_sum_le _ _
    _ = ∑ j, weight j*‖A‖ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [norm_smul,Real.norm_of_nonneg (hw j),markedMinorMatrix_submatrix_equiv_pair_norm]
    _ = _ := by rw [← Finset.sum_mul,hmass,one_mul]

end ArtinMatthews
