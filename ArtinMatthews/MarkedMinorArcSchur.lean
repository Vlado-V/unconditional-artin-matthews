module

public import ArtinMatthews.MarkedMinorArcWeightedConjugation


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine asymmetric finite weighted complex Schur bounds. -/
noncomputable section
namespace ArtinMatthews

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

theorem markedSchur_row_cauchy {ι : Type*} [Fintype ι]
    (μ w r x : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i) (hw : ∀ i, 0 < w i) (hr : ∀ i, 0 ≤ r i) :
    (∑ i, Real.sqrt (μ i)*r i*x i)^2 ≤
      (∑ i, μ i*r i*w i)*(∑ i, r i*(x i)^2/w i) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro i _
    exact mul_nonneg (mul_nonneg (hμ i) (hr i)) (hw i).le
  · intro i _
    exact div_nonneg (mul_nonneg (hr i) (sq_nonneg _)) (hw i).le
  · intro i _
    simp only [mul_pow,Real.sq_sqrt (hμ i)]
    apply le_of_eq
    field_simp [(hw i).ne']

/-- The counting matrix is the actual square-root conjugation of the kernel
acting in the finite measure μ. Zero atoms are permitted. -/
theorem markedSchur_counting_energy {ι : Type*} [Fintype ι]
    (μ w : ι → ℝ) (K : Matrix ι ι ℂ) (hμ : ∀ i, 0 ≤ μ i) (hw : ∀ i, 0 < w i)
    {R C : ℝ} (hR : 0 ≤ R)
    (hrow : ∀ i, (∑ j, μ j*‖K i j‖*w j) ≤ R*w i)
    (hcol : ∀ j, (∑ i, μ i*‖K i j‖*w i) ≤ C*w j) (x : ι → ℂ) :
    (∑ i, ‖(markedWeightedCountingMatrix μ K *ᵥ x) i‖^2) ≤ R*C*(∑ j, ‖x j‖^2) := by
  have hscalar (i : ι) : ‖(Real.sqrt (μ i):ℂ)‖ = Real.sqrt (μ i) := by
    simp only [Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have hpoint (i : ι) : ‖(markedWeightedCountingMatrix μ K *ᵥ x) i‖^2 ≤
      R*∑ j, μ i*‖K i j‖*w i*(‖x j‖^2/w j) := by
    have ht : ‖(markedWeightedCountingMatrix μ K *ᵥ x) i‖ ≤
        Real.sqrt (μ i)*(∑ j, Real.sqrt (μ j)*‖K i j‖*‖x j‖) := by
      calc
        _ ≤ ∑ j, ‖markedWeightedCountingMatrix μ K i j*x j‖ := norm_sum_le _ _
        _ = _ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          simp only [markedWeightedCountingMatrix,norm_mul,hscalar]
          ring
    have hs0 : 0 ≤ ∑ j, Real.sqrt (μ j)*‖K i j‖*‖x j‖ :=
      Finset.sum_nonneg (fun j _ => by positivity)
    have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hs0)).mpr ht
    rw [mul_pow,Real.sq_sqrt (hμ i)] at hs
    have hc := markedSchur_row_cauchy μ w (fun j => ‖K i j‖) (fun j => ‖x j‖)
      hμ hw (fun j => norm_nonneg _)
    have hg0 : 0 ≤ ∑ j, ‖K i j‖*‖x j‖^2/w j :=
      Finset.sum_nonneg (fun j _ => div_nonneg (mul_nonneg (norm_nonneg _) (sq_nonneg _)) (hw j).le)
    calc
      _ ≤ μ i*((∑ j, μ j*‖K i j‖*w j)*(∑ j, ‖K i j‖*‖x j‖^2/w j)) :=
        hs.trans (mul_le_mul_of_nonneg_left hc (hμ i))
      _ ≤ μ i*((R*w i)*(∑ j, ‖K i j‖*‖x j‖^2/w j)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hrow i) hg0) (hμ i)
      _ = _ := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  calc
    _ ≤ ∑ i, R*∑ j, μ i*‖K i j‖*w i*(‖x j‖^2/w j) :=
      Finset.sum_le_sum (fun i _ => hpoint i)
    _ = R*∑ j, (‖x j‖^2/w j)*(∑ i, μ i*‖K i j‖*w i) := by
      rw [← Finset.mul_sum,Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ R*∑ j, (‖x j‖^2/w j)*(C*w j) := by
      apply mul_le_mul_of_nonneg_left _ hR
      exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hcol j)
        (div_nonneg (sq_nonneg _) (hw j).le))
    _ = R*C*(∑ j, ‖x j‖^2) := by
      rw [mul_assoc]
      congr 1
      calc
        _ = ∑ j, C*‖x j‖^2 := by
          apply Finset.sum_congr rfl
          intro j _
          field_simp [(hw j).ne']
        _ = _ := (Finset.mul_sum _ _ _).symm

theorem markedSchur_counting_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ w : ι → ℝ) (K : Matrix ι ι ℂ) (hμ : ∀ i, 0 ≤ μ i) (hw : ∀ i, 0 < w i)
    {R C : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hrow : ∀ i, (∑ j, μ j*‖K i j‖*w j) ≤ R*w i)
    (hcol : ∀ j, (∑ i, μ i*‖K i j‖*w i) ≤ C*w j) :
    ‖markedWeightedCountingMatrix μ K‖ ≤ Real.sqrt (R*C) := by
  apply markedMinorMatrix_norm_le_of_energy _ (Real.sqrt_nonneg _)
  intro x
  rw [Real.sq_sqrt (mul_nonneg hR hC)]
  exact markedSchur_counting_energy μ w K hμ hw hR hrow hcol x

theorem markedSchur_weighted_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ w : ι → ℝ) (K : Matrix ι ι ℂ) (hμ : ∀ i, 0 ≤ μ i) (hw : ∀ i, 0 < w i)
    {R C : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hrow : ∀ i, (∑ j, μ j*‖K i j‖*w j) ≤ R*w i)
    (hcol : ∀ j, (∑ i, μ i*‖K i j‖*w i) ≤ C*w j) (f : ι → ℂ) :
    (∑ i, μ i*‖markedWeightedMatrixApply μ K f i‖^2) ≤ R*C*(∑ j, μ j*‖f j‖^2) := by
  have hh := markedWeightedMatrix_energy_le_of_counting_norm μ hμ K (Real.sqrt_nonneg _)
    (markedSchur_counting_norm_le μ w K hμ hw hR hC hrow hcol) f
  simpa only [Real.sq_sqrt (mul_nonneg hR hC)] using hh

end ArtinMatthews
