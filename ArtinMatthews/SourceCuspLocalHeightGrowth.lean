module

public import ArtinMatthews.SourceArchMatrixHeight
public import ArtinMatthews.SourceKPCommRingDiagonal
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual inverse-entry height constant grows polynomially along positive diagonal rays. -/
namespace ArtinMatthews.SourceArchJacquet
open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups
noncomputable section

theorem sourceKPEntryBound_left_diagonal_inverse (g : GL (Fin 2) ℂ)
    (a : ℂˣ) (ha : 1 ≤ ‖(a : ℂ)‖) :
    sourceKPEntryBound (sourceKPDiagonalHom ℂ a⁻¹ * g) ≤ sourceKPEntryBound g := by
  have hainv : ‖((a⁻¹ : ℂˣ) : ℂ)‖ ≤ 1 := by
    rw [Units.val_inv_eq_inv_val, norm_inv]
    exact inv_le_one_of_one_le₀ ha
  have hentry (i j : Fin 2) :
      ‖(sourceKPDiagonalHom ℂ a⁻¹ * g) i j‖ ≤ sourceKPEntryBound g := by
    fin_cases i
    · change ‖(sourceKPDiagonalHom ℂ a⁻¹ * g) 0 j‖ ≤ sourceKPEntryBound g
      have he : (sourceKPDiagonalHom ℂ a⁻¹ * g) 0 j = ((a⁻¹ : ℂˣ) : ℂ) * g 0 j := by
        simp [sourceKPDiagonalHom, Matrix.mul_apply, Fin.sum_univ_two]
      rw [he, norm_mul]
      exact (mul_le_mul_of_nonneg_right hainv (norm_nonneg _)).trans
        (by simpa only [one_mul] using sourceKPEntryBound_entry g 0 j)
    · change ‖(sourceKPDiagonalHom ℂ a⁻¹ * g) 1 j‖ ≤ sourceKPEntryBound g
      have he : (sourceKPDiagonalHom ℂ a⁻¹ * g) 1 j = g 1 j := by
        simp [sourceKPDiagonalHom, Matrix.mul_apply, Fin.sum_univ_two]
      rw [he]
      exact sourceKPEntryBound_entry g 1 j
  exact max_le (sourceKPEntryBound_one_le g)
    (max_le (max_le (hentry 0 0) (hentry 0 1)) (max_le (hentry 1 0) (hentry 1 1)))

theorem sourceArchMatrixHeightConstant_right_diagonal (g : GL (Fin 2) ℂ)
    (a : ℂˣ) (ha : 1 ≤ ‖(a : ℂ)‖) :
    sourceArchMatrixHeightConstant (g * sourceKPDiagonalHom ℂ a) ≤
      ‖(a : ℂ)‖ * sourceArchMatrixHeightConstant g := by
  have hinv : (g * sourceKPDiagonalHom ℂ a)⁻¹ = sourceKPDiagonalHom ℂ a⁻¹ * g⁻¹ := by
    rw [_root_.mul_inv_rev, map_inv]
  have hM : sourceKPEntryBound (g * sourceKPDiagonalHom ℂ a)⁻¹ ≤ sourceKPEntryBound g⁻¹ := by
    rw [hinv]
    exact sourceKPEntryBound_left_diagonal_inverse g⁻¹ a ha
  have hdet : (GeneralLinearGroup.det (sourceKPDiagonalHom ℂ a) : ℂ) = a := by
    simp [sourceKPDiagonalHom, GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  unfold sourceArchMatrixHeightConstant
  rw [map_mul, Units.val_mul, norm_mul, hdet]
  apply max_le
  · have hm : 1 ≤ max 1 (4 * ‖(GeneralLinearGroup.det g : ℂ)‖ * sourceKPEntryBound g⁻¹ ^ 2) :=
      le_max_left _ _
    exact hm.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right ha (le_trans zero_le_one hm))
  · calc
      _ = ‖(a : ℂ)‖ * (4 * ‖(GeneralLinearGroup.det g : ℂ)‖ *
          sourceKPEntryBound (g * sourceKPDiagonalHom ℂ a)⁻¹ ^ 2) := by ring
      _ ≤ ‖(a : ℂ)‖ * (4 * ‖(GeneralLinearGroup.det g : ℂ)‖ * sourceKPEntryBound g⁻¹ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀
          (le_trans zero_le_one (sourceKPEntryBound_one_le _)) hM 2
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg _)

end
end ArtinMatthews.SourceArchJacquet
