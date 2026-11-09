module

public import ArtinMatthews.CubicThetaSiegelData
public import OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction


set_option backward.privateInPublic true
@[expose] public section

/-! Restriction of the actual rational symplectic action to the Eisenstein Siegel line. -/
noncomputable section
namespace ArtinMatthews

open Matrix Complex UpperHalfPlane
open scoped Matrix MatrixGroups
open OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData
open OAI.AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM

private theorem siegel_eq_of_matrix_eq
    {Z W : OAI.AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin 2)}
    (h : Z.matrix = W.matrix) : Z = W := by
  cases Z
  cases W
  cases h
  rfl

private theorem eisensteinRealBlocks_A (γ : SL(2, ℚ)) :
    (realBlocks (eisensteinSymplectic γ)).complexify.A =
      (γ 0 0 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realBlocks, blocks, mapSp, eisensteinSymplectic, eisensteinSymplecticMatrix,
      SymplecticBlocks.complexify, Matrix.fromBlocks_map]

private theorem eisensteinRealBlocks_B (γ : SL(2, ℚ)) :
    (realBlocks (eisensteinSymplectic γ)).complexify.B =
      (γ 0 1 : ℂ) • eisensteinGram.map (algebraMap ℚ ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realBlocks, blocks, mapSp, eisensteinSymplectic, eisensteinSymplecticMatrix,
      SymplecticBlocks.complexify, Matrix.fromBlocks_map, eisensteinGram]

private theorem eisensteinRealBlocks_C (γ : SL(2, ℚ)) :
    (realBlocks (eisensteinSymplectic γ)).complexify.C =
      (γ 1 0 : ℂ) • eisensteinGramInv.map (algebraMap ℚ ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realBlocks, blocks, mapSp, eisensteinSymplectic, eisensteinSymplecticMatrix,
      SymplecticBlocks.complexify, Matrix.fromBlocks_map, eisensteinGramInv]

private theorem eisensteinRealBlocks_D (γ : SL(2, ℚ)) :
    (realBlocks (eisensteinSymplectic γ)).complexify.D =
      (γ 1 1 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realBlocks, blocks, mapSp, eisensteinSymplectic, eisensteinSymplecticMatrix,
      SymplecticBlocks.complexify, Matrix.fromBlocks_map]

theorem eisensteinSiegel_numerator (γ : SL(2, ℚ)) (τ : ℍ) :
    (realBlocks (eisensteinSymplectic γ)).complexify.numerator
      (eisensteinSiegel τ).matrix =
        ((γ 0 0 : ℂ) * τ + (γ 0 1 : ℂ)) •
          eisensteinGram.map (algebraMap ℚ ℂ) := by
  rw [SymplecticBlocks.numerator, eisensteinRealBlocks_A, eisensteinRealBlocks_B]
  change (γ 0 0 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) *
    ((τ : ℂ) • eisensteinGram.map (algebraMap ℚ ℂ)) + _ = _
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
  rw [← add_smul, mul_comm (τ : ℂ)]

theorem eisensteinSiegel_denominator (γ : SL(2, ℚ)) (τ : ℍ) :
    (realBlocks (eisensteinSymplectic γ)).complexify.denominator
      (eisensteinSiegel τ).matrix =
        ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) •
          (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [SymplecticBlocks.denominator, eisensteinRealBlocks_C, eisensteinRealBlocks_D]
  change (γ 1 0 : ℂ) • eisensteinGramInv.map (algebraMap ℚ ℂ) *
    ((τ : ℂ) • eisensteinGram.map (algebraMap ℚ ℂ)) + _ = _
  have hG : eisensteinGramInv.map (algebraMap ℚ ℂ) *
      eisensteinGram.map (algebraMap ℚ ℂ) = 1 := by
    rw [← Matrix.map_mul, eisensteinGramInv_mul]
    simp
  simp only [Matrix.smul_mul, Matrix.mul_smul, hG, smul_smul]
  rw [← add_smul, mul_comm (τ : ℂ)]

/-- The determinant factor restricts to the square of the classical weight-one factor. -/
theorem eisensteinSiegel_denominator_det (γ : SL(2, ℚ)) (τ : ℍ) :
    ((realBlocks (eisensteinSymplectic γ)).complexify.denominator
      (eisensteinSiegel τ).matrix).det =
        ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) ^ 2 := by
  rw [eisensteinSiegel_denominator, Matrix.det_smul]
  simp

/-- The actual symplectic fractional action is the classical Möbius action
on the Eisenstein Siegel line. -/
theorem eisensteinSiegel_transform (γ : SL(2, ℚ)) (τ : ℍ) :
    (realBlocks (eisensteinSymplectic γ)).transformSiegel (eisensteinSiegel τ) =
      eisensteinSiegel (γ • τ) := by
  have hdet := (realBlocks (eisensteinSymplectic γ)).denominator_det_isUnit
    (eisensteinSiegel τ)
  rw [eisensteinSiegel_denominator_det] at hdet
  have hc : (γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ) ≠ 0 := by
    exact fun h => hdet.ne_zero (by simp [h])
  have hi : (((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) •
      (1 : Matrix (Fin 2) (Fin 2) ℂ))⁻¹ =
      (((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ))⁻¹) •
        (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    apply Matrix.inv_eq_right_inv
    simp [smul_smul, hc]
  apply siegel_eq_of_matrix_eq
  change (realBlocks (eisensteinSymplectic γ)).complexify.fractional
    (eisensteinSiegel τ).matrix = eisensteinSiegelMatrix (γ • τ)
  rw [SymplecticBlocks.fractional, eisensteinSiegel_numerator,
    eisensteinSiegel_denominator, hi]
  simp only [Matrix.mul_smul, Matrix.mul_one, smul_smul]
  unfold eisensteinSiegelMatrix
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  have hcast (q : ℚ) : ((algebraMap ℚ ℝ q : ℝ) : ℂ) = (q : ℂ) := by simp
  simp only [hcast]
  rw [div_eq_mul_inv, mul_comm]

/-- The normalized determinant square is exactly the classical factor squared. -/
theorem eisensteinSiegel_halfDet_sq (γ : SL(2, ℚ)) (τ : ℍ) :
    halfDet (realBlocks (eisensteinSymplectic γ)) (eisensteinSiegel τ) ^ 2 =
      ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) ^ 2 := by
  rw [halfDet_sq, eisensteinSiegel_denominator_det]

end ArtinMatthews
