module

public import ArtinMatthews.MarkedMinorArcOperator
public import Mathlib.LinearAlgebra.Matrix.Block


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite direct-sum transport for the genuine L2 matrix norm. -/
namespace ArtinMatthews

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

theorem markedMinorMatrix_energy_le_of_norm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) {C : ℝ} (hC : 0 ≤ C) (hA : ‖A‖ ≤ C) (f : ι → ℂ) :
    (∑ i, ‖(A *ᵥ f) i‖^2) ≤ C^2*(∑ i, ‖f i‖^2) := by
  have hh := (A.l2_opNorm_mulVec ((EuclideanSpace.equiv ι ℂ).symm f)).trans
    (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mpr hh
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at hs
  exact hs

theorem markedMinorBlockDiagonal_mulVec {J : Type*} [Fintype J] [DecidableEq J]
    {ι : J → Type*} [∀ j, Fintype (ι j)]
    (A : ∀ j, Matrix (ι j) (ι j) ℂ) (f : (Σ j, ι j) → ℂ) (j : J) (i : ι j) :
    (Matrix.blockDiagonal' A *ᵥ f) ⟨j,i⟩ = (A j *ᵥ fun k => f ⟨j,k⟩) i := by
  classical
  simp only [Matrix.mulVec, dotProduct, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  rw [Fintype.sum_eq_single j]
  · simp only [Matrix.blockDiagonal'_apply_eq]
  · intro j' hj'
    apply Finset.sum_eq_zero
    intro k _
    rw [Matrix.blockDiagonal'_apply_ne A i k hj'.symm, zero_mul]

/-- A dependent direct sum of uniformly bounded blocks has the same operator
bound. The proof sums the actual coordinate energies, so there is no loss
depending on the number or dimensions of the blocks. -/
theorem markedMinorBlockDiagonal_norm_le {J : Type*} [Fintype J] [DecidableEq J]
    {ι : J → Type*} [∀ j, Fintype (ι j)] [∀ j, DecidableEq (ι j)]
    (A : ∀ j, Matrix (ι j) (ι j) ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ j, ‖A j‖ ≤ C) : ‖Matrix.blockDiagonal' A‖ ≤ C := by
  classical
  apply markedMinorMatrix_norm_le_of_energy _ hC
  intro f
  simp only [← Finset.univ_sigma_univ, Finset.sum_sigma, markedMinorBlockDiagonal_mulVec]
  calc
    _ ≤ ∑ j, C^2 * ∑ k, ‖f ⟨j,k⟩‖^2 :=
      Finset.sum_le_sum (fun j _ => markedMinorMatrix_energy_le_of_norm (A j) hC (hA j) _)
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem markedMinorMatrix_submatrix_equiv_norm_le {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (e : κ ≃ ι) : ‖A.submatrix e e‖ ≤ ‖A‖ := by
  apply markedMinorMatrix_norm_le_of_energy _ (norm_nonneg A)
  intro f
  rw [Matrix.submatrix_mulVec_equiv A f e e]
  calc
    _ = ∑ i : ι, ‖(A *ᵥ (f ∘ e.symm)) i‖^2 :=
      e.sum_comp (fun i => ‖(A *ᵥ (f ∘ e.symm)) i‖^2)
    _ ≤ ‖A‖^2 * ∑ i : ι, ‖(f ∘ e.symm) i‖^2 :=
      markedMinorMatrix_energy_le_of_norm A (norm_nonneg _) le_rfl _
    _ = _ := by
      rw [← e.sum_comp (fun i => ‖(f ∘ e.symm) i‖^2)]
      simp only [Function.comp_apply, Equiv.symm_apply_apply]

/-- Simultaneous finite row and column permutation preserves the actual L2
operator norm. -/
theorem markedMinorMatrix_submatrix_equiv_norm {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (e : κ ≃ ι) : ‖A.submatrix e e‖ = ‖A‖ := by
  apply le_antisymm (markedMinorMatrix_submatrix_equiv_norm_le A e)
  have hh := markedMinorMatrix_submatrix_equiv_norm_le (A.submatrix e e) e.symm
  have he : (A.submatrix e e).submatrix e.symm e.symm = A := by
    ext i j
    simp
  rw [he] at hh
  exact hh

/-- A genuine finite convex average of permutation conjugates is a
contraction in the actual L2 operator norm. -/
theorem markedMinorMatrix_average_permutations_norm_le {ι J : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype J]
    (A : Matrix ι ι ℂ) (e : J → Equiv.Perm ι) (weight : J → ℝ)
    (hw : ∀ j, 0 ≤ weight j) (hmass : ∑ j, weight j = 1) :
    ‖∑ j, (weight j) • A.submatrix (e j) (e j)‖ ≤ ‖A‖ := by
  calc
    _ ≤ ∑ j, ‖(weight j) • A.submatrix (e j) (e j)‖ := norm_sum_le _ _
    _ = ∑ j, weight j * ‖A‖ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [norm_smul, Real.norm_of_nonneg (hw j), markedMinorMatrix_submatrix_equiv_norm]
    _ = ‖A‖ := by rw [← Finset.sum_mul, hmass, one_mul]

end ArtinMatthews
