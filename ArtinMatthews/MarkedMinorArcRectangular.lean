module

public import ArtinMatthews.MarkedMinorArcCompression


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine rectangular finite L² transport, with no dimension loss. -/
namespace ArtinMatthews

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

theorem markedMinorRectangular_norm_le_of_energy {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (A : Matrix ι κ ℂ) {C : ℝ} (hC : 0 ≤ C)
    (henergy : ∀ f : κ → ℂ, (∑ i, ‖(A *ᵥ f) i‖^2) ≤ C^2*(∑ j, ‖f j‖^2)) :
    ‖A‖ ≤ C := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  rw [mul_pow,EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq]
  exact henergy (WithLp.ofLp x)

theorem markedMinorRectangular_energy_le_of_norm {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (A : Matrix ι κ ℂ) {C : ℝ} (hC : 0 ≤ C) (hA : ‖A‖ ≤ C) (f : κ → ℂ) :
    (∑ i, ‖(A *ᵥ f) i‖^2) ≤ C^2*(∑ j, ‖f j‖^2) := by
  have hh := (A.l2_opNorm_mulVec ((EuclideanSpace.equiv κ ℂ).symm f)).trans
    (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mpr hh
  rw [mul_pow,EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq] at hs
  exact hs

theorem markedMinorRectangularBlockDiagonal_mulVec {J : Type*} [Fintype J] [DecidableEq J]
    {ι κ : J → Type*} [∀ j, Fintype (κ j)]
    (A : ∀ j, Matrix (ι j) (κ j) ℂ) (f : (Σ j, κ j) → ℂ) (j : J) (i : ι j) :
    (Matrix.blockDiagonal' A *ᵥ f) ⟨j,i⟩ = (A j *ᵥ fun k => f ⟨j,k⟩) i := by
  classical
  simp only [Matrix.mulVec,dotProduct,← Finset.univ_sigma_univ,Finset.sum_sigma]
  rw [Fintype.sum_eq_single j]
  · simp only [Matrix.blockDiagonal'_apply_eq]
  · intro j' hj'
    apply Finset.sum_eq_zero
    intro k _
    rw [Matrix.blockDiagonal'_apply_ne A i k hj'.symm,zero_mul]

theorem markedMinorRectangularBlockDiagonal_norm_le {J : Type*} [Fintype J] [DecidableEq J]
    {ι κ : J → Type*} [∀ j, Fintype (ι j)] [∀ j, Fintype (κ j)]
    [∀ j, DecidableEq (κ j)] (A : ∀ j, Matrix (ι j) (κ j) ℂ)
    {C : ℝ} (hC : 0 ≤ C) (hA : ∀ j, ‖A j‖ ≤ C) : ‖Matrix.blockDiagonal' A‖ ≤ C := by
  classical
  apply markedMinorRectangular_norm_le_of_energy _ hC
  intro f
  simp only [← Finset.univ_sigma_univ,Finset.sum_sigma,markedMinorRectangularBlockDiagonal_mulVec]
  calc
    _ ≤ ∑ j, C^2*∑ k, ‖f ⟨j,k⟩‖^2 :=
      Finset.sum_le_sum (fun j _ => markedMinorRectangular_energy_le_of_norm (A j) hC (hA j) _)
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem markedMinorRectangularSubmatrix_mulVec {ι κ ι' κ' : Type*}
    [Fintype κ] [Fintype κ'] (A : Matrix ι κ ℂ)
    (er : ι' → ι) (ec : κ' → κ) (hc : Function.Injective ec) (f : κ' → ℂ) (i : ι') :
    (A *ᵥ Function.extend ec f 0) (er i) = (A.submatrix er ec *ᵥ f) i := by
  classical
  unfold Matrix.mulVec dotProduct
  rw [markedMinorSum_injective ec hc _ (fun j hj => by
    rw [Function.extend_apply' _ _ _ hj]
    simp)]
  simp only [hc.extend_apply,Matrix.submatrix_apply]

theorem markedMinorRectangularSubmatrix_norm_le {ι κ ι' κ' : Type*}
    [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ'] [DecidableEq κ] [DecidableEq κ']
    (A : Matrix ι κ ℂ) (er : ι' → ι) (ec : κ' → κ)
    (hr : Function.Injective er) (hc : Function.Injective ec) : ‖A.submatrix er ec‖ ≤ ‖A‖ := by
  classical
  apply markedMinorRectangular_norm_le_of_energy _ (norm_nonneg _)
  intro f
  have hh := markedMinorRectangular_energy_le_of_norm A (norm_nonneg _) le_rfl (Function.extend ec f 0)
  rw [markedMinorExtend_energy ec hc f] at hh
  calc
    _ = ∑ i, ‖(A *ᵥ Function.extend ec f 0) (er i)‖^2 := by
      simp only [markedMinorRectangularSubmatrix_mulVec A er ec hc f]
    _ = ∑ i ∈ Finset.univ.image er, ‖(A *ᵥ Function.extend ec f 0) i‖^2 :=
      (Finset.sum_image (s := Finset.univ) (g := er)
        (f := fun i => ‖(A *ᵥ Function.extend ec f 0) i‖^2) (fun _ _ _ _ h => hr h)).symm
    _ ≤ ∑ i, ‖(A *ᵥ Function.extend ec f 0) i‖^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
    _ ≤ _ := hh

end ArtinMatthews
