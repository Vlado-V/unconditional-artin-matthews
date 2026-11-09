module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Group.InfiniteSum


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open scoped BigOperators ENNReal
noncomputable section

/-- The exact ℓ¹ weight-separation cost in a finite lattice row space.
This preserves the square-moment exponent and introduces no row count. -/
theorem sourcePoissonFiniteL2_fourier_cost
    {I J : Type} [Fintype I] (f g : J → I → ℂ) (C : J → ℝ)
    (hC : Summable C) (hC₀ : ∀ j, 0 ≤ C j) (hf : ∀ j i, ‖f j i‖ ≤ C j)
    (B : ℝ) (hB : 0 ≤ B) (hg : ∀ j, ∑ i, ‖g j i‖ ^ 2 ≤ B) :
    (∑ i, ‖∑' j, f j i * g j i‖ ^ 2) ≤ (∑' j, C j) ^ 2 * B := by
  let a (j : J) : EuclideanSpace ℂ I := WithLp.toLp 2 (fun i => f j i * g j i)
  have hNorm (j : J) : ‖a j‖ ≤ C j * Real.sqrt B := by
    apply (sq_le_sq₀ (norm_nonneg (a j)) (mul_nonneg (hC₀ j) (Real.sqrt_nonneg B))).mp
    rw [EuclideanSpace.norm_sq_eq, mul_pow, Real.sq_sqrt hB]
    calc
      _ ≤ ∑ i, (C j) ^ 2 * ‖g j i‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        change ‖f j i * g j i‖ ^ 2 ≤ _
        rw [norm_mul, mul_pow]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg (f j i)) (hf j i) 2) (sq_nonneg _)
      _ = (C j) ^ 2 * ∑ i, ‖g j i‖ ^ 2 := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hg j) (sq_nonneg _)
  have hMajor : Summable (fun j => C j * Real.sqrt B) := hC.mul_right _
  have ha : Summable (fun j => ‖a j‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg (a j)) hNorm hMajor
  have hSum : ‖∑' j, a j‖ ≤ (∑' j, C j) * Real.sqrt B := by
    calc
      _ ≤ ∑' j, ‖a j‖ := norm_tsum_le_tsum_norm ha
      _ ≤ ∑' j, C j * Real.sqrt B := ha.tsum_le_tsum hNorm hMajor
      _ = _ := tsum_mul_right
  have hPoint (i : I) :
      (∑' j, a j) i = ∑' j, f j i * g j i :=
    (EuclideanSpace.proj i).map_tsum ha.of_norm
  have hTotal := (sq_le_sq₀ (norm_nonneg (∑' j, a j))
    (mul_nonneg (tsum_nonneg hC₀) (Real.sqrt_nonneg B))).mpr hSum
  rw [EuclideanSpace.norm_sq_eq, mul_pow, Real.sq_sqrt hB] at hTotal
  simpa only [hPoint] using hTotal

end
end ArtinMatthews.SourceEulerAssembly
