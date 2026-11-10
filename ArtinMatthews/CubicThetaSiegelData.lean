module

public import ArtinMatthews.CubicThetaSymplecticEmbedding
public import OAI.AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! The actual positive Siegel matrix for the Eisenstein norm lattice. -/
noncomputable section
namespace ArtinMatthews

open Matrix Complex UpperHalfPlane
open scoped Matrix MatrixGroups
open OAI.AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM

/-- The Eisenstein norm embeds the upper half plane into genus two. -/
def eisensteinSiegelMatrix (τ : ℍ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (τ : ℂ) • eisensteinGram.map (algebraMap ℚ ℂ)

theorem eisensteinSiegelMatrix_symmetric (τ : ℍ) :
    (eisensteinSiegelMatrix τ).IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eisensteinSiegelMatrix, eisensteinGram]

theorem eisensteinSiegelMatrix_imaginary_posDef (τ : ℍ) :
    Matrix.PosDef (fun i j => (eisensteinSiegelMatrix τ i j).im) := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    change (eisensteinSiegelMatrix τ j i).im = (eisensteinSiegelMatrix τ i j).im
    fin_cases i <;> fin_cases j <;>
      simp [eisensteinSiegelMatrix, eisensteinGram]
  · intro x hx
    have hx' : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra h
      push Not at h
      apply hx
      ext i
      fin_cases i <;> simp [h.1, h.2]
    have hnorm : 0 < (x 0) ^ 2 + (x 1) ^ 2 := by
      rcases hx' with h | h
      · have := sq_pos_of_ne_zero h
        nlinarith [sq_nonneg (x 1)]
      · have := sq_pos_of_ne_zero h
        nlinarith [sq_nonneg (x 0)]
    have hp := mul_pos τ.im_pos hnorm
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
    simp [eisensteinSiegelMatrix, eisensteinGram]
    nlinarith [mul_nonneg τ.im_pos.le (sq_nonneg (x 0 - x 1))]

/-- An actual Siegel point, including its proved positivity. -/
def eisensteinSiegel (τ : ℍ) : SiegelMatrix (Fin 2) where
  matrix := eisensteinSiegelMatrix τ
  symmetric := eisensteinSiegelMatrix_symmetric τ
  imaginary_posDef := eisensteinSiegelMatrix_imaginary_posDef τ

/-- The matrix phase is exactly twice the Eisenstein quadratic norm. -/
theorem eisensteinSiegel_form (τ : ℍ) (x : Fin 2 → ℝ) :
    siegelMatrixForm (eisensteinSiegel τ).matrix x x =
      2 * (τ : ℂ) * ((x 0 : ℂ)^2 - (x 0 : ℂ)*(x 1 : ℂ) + (x 1 : ℂ)^2) := by
  simp [siegelMatrixForm_apply, eisensteinSiegel, eisensteinSiegelMatrix,
    eisensteinGram, Fin.sum_univ_two]
  ring

end ArtinMatthews
