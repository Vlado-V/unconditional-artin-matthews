module

public import Mathlib.LinearAlgebra.SymplecticGroup
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt


set_option backward.privateInPublic true
@[expose] public section

/-!
The rational symplectic embedding associated to the actual Eisenstein norm.
The two-dimensional Siegel line has Gram matrix `[[2,-1],[-1,2]]`.
These are coordinate identities, independent of any asserted theta automorphy.
-/

namespace ArtinMatthews

open Matrix
open scoped Matrix MatrixGroups

/-- Twice the quadratic form `x² - xy + y²`. -/
def eisensteinGram : Matrix (Fin 2) (Fin 2) ℚ := !![2, -1; -1, 2]

/-- The inverse Gram matrix, with denominator exactly three. -/
def eisensteinGramInv : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(2 : ℚ) / 3, 1 / 3; 1 / 3, 2 / 3]

@[simp] theorem eisensteinGram_transpose : eisensteinGramᵀ = eisensteinGram := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [eisensteinGram, eisensteinGramInv, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem eisensteinGramInv_transpose : eisensteinGramInvᵀ = eisensteinGramInv := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [eisensteinGram, eisensteinGramInv, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem eisensteinGram_mul_inv : eisensteinGram * eisensteinGramInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [eisensteinGram, eisensteinGramInv, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem eisensteinGramInv_mul : eisensteinGramInv * eisensteinGram = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [eisensteinGram, eisensteinGramInv, Matrix.mul_apply, Fin.sum_univ_two]

/-- The block embedding that preserves the Eisenstein Siegel line. -/
def eisensteinSymplecticMatrix (γ : SL(2, ℚ)) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ :=
  Matrix.fromBlocks (γ 0 0 • (1 : Matrix (Fin 2) (Fin 2) ℚ))
    (γ 0 1 • eisensteinGram) (γ 1 0 • eisensteinGramInv)
    (γ 1 1 • (1 : Matrix (Fin 2) (Fin 2) ℚ))

theorem eisensteinSymplecticMatrix_mem (γ : SL(2, ℚ)) :
    eisensteinSymplecticMatrix γ ∈ Matrix.symplecticGroup (Fin 2) ℚ := by
  rw [eisensteinSymplecticMatrix, SymplecticGroup.fromBlocks_mem_iff]
  have hdet : γ 0 0 * γ 1 1 - γ 1 0 * γ 0 1 = 1 := by
    simpa only [Matrix.det_fin_two, mul_comm (γ 0 1) (γ 1 0)] using γ.property
  simp only [transpose_smul, transpose_one, eisensteinGram_transpose,
    eisensteinGramInv_transpose, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, eisensteinGramInv_mul, smul_smul]
  constructor
  · congr 1
    ring
  constructor
  · congr 1
    ring
  · rw [← sub_smul]
    have he : γ 1 1 * γ 0 0 - γ 0 1 * γ 1 0 = 1 := by nlinarith [hdet]
    rw [he, one_smul]

/-- An actual rational symplectic matrix, with no modularity hypothesis. -/
def eisensteinSymplectic (γ : SL(2, ℚ)) : Matrix.symplecticGroup (Fin 2) ℚ :=
  ⟨eisensteinSymplecticMatrix γ, eisensteinSymplecticMatrix_mem γ⟩

@[simp] theorem eisensteinSymplectic_one :
    eisensteinSymplectic (1 : SL(2, ℚ)) = 1 := by
  apply Subtype.ext
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [eisensteinSymplectic, eisensteinSymplecticMatrix,
      eisensteinGram, eisensteinGramInv, Matrix.fromBlocks]

theorem eisensteinSymplectic_mul (γ δ : SL(2, ℚ)) :
    eisensteinSymplectic (γ * δ) = eisensteinSymplectic γ * eisensteinSymplectic δ := by
  apply Subtype.ext
  change eisensteinSymplecticMatrix (γ * δ) =
    eisensteinSymplecticMatrix γ * eisensteinSymplecticMatrix δ
  simp only [eisensteinSymplecticMatrix, Matrix.fromBlocks_multiply,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    eisensteinGram_mul_inv, eisensteinGramInv_mul, smul_smul]
  apply Matrix.fromBlocks_inj.mpr
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [← add_smul] <;> congr 1 <;>
    change (γ.val * δ.val) _ _ = _ <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The actual homomorphism used to restrict rational Siegel automorphy
 to the classical upper half plane. -/
def eisensteinSymplecticHom : SL(2, ℚ) →* Matrix.symplecticGroup (Fin 2) ℚ where
  toFun := eisensteinSymplectic
  map_one' := eisensteinSymplectic_one
  map_mul' := eisensteinSymplectic_mul

end ArtinMatthews
