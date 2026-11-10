module

public import ArtinMatthews.SourceProjectiveBruhat
public import ArtinMatthews.SourceKubotaBottomRows
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! Actual rank-two generation by the upper root, diagonal, scalars and
the Weyl element. The nontriangular reduction is a literal row operation;
there is no premise that the abstract generators cover GL2. -/

namespace ArtinMatthews
open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups
noncomputable section
variable {F : Type*} [Field F]

theorem sourceGL2Upper_mul (x y : F) :
    sourceGL2Upper x * sourceGL2Upper y = sourceGL2Upper (x + y) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceGL2Upper, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem sourceGL2Upper_zero : sourceGL2Upper (0 : F) = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sourceGL2Upper]

theorem sourceGL2Weyl_square : (sourceGL2Weyl : GL (Fin 2) F) * sourceGL2Weyl = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sourceGL2Weyl, Matrix.mul_apply, Fin.sum_univ_two]

theorem sourceGL2_triangular_factor (g : GL (Fin 2) F) (hg : g 1 0 = 0) :
    ∃ (x : F) (u d : Fˣ),
      g = sourceGL2Upper x * sourceGL2Diagonal u * GeneralLinearGroup.scalar (Fin 2) d := by
  have hd0 := sourceGL2_bottom_right_ne_zero g hg
  let d := Units.mk0 (g 1 1) hd0
  let u := GeneralLinearGroup.det g / d ^ 2
  have hd : (d : F) = g 1 1 := rfl
  have hu : (u : F) = g 0 0 / g 1 1 := by
    dsimp only [u]
    rw [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val, hd, sourceGL2_det_val, hg, mul_zero, sub_zero]
    field_simp [hd0]
  refine ⟨g 0 1 / g 1 1, u, d, ?_⟩
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceGL2Upper, sourceGL2Diagonal, Matrix.mul_apply,
      GeneralLinearGroup.coe_scalar, Matrix.diagonal_apply, hd, hu, hg, hd0]

theorem sourceGL2_weyl_factor (g : GL (Fin 2) F) (hg : g 1 0 ≠ 0) :
    ∃ (b : GL (Fin 2) F) (x : F), b 1 0 = 0 ∧
      g = b * sourceGL2Weyl * sourceGL2Upper x := by
  let x := g 1 1 / g 1 0
  let b := g * sourceGL2Upper (-x) * sourceGL2Weyl
  refine ⟨b, x, ?_, ?_⟩
  · change (g * sourceGL2Upper (-x) * (sourceGL2Weyl : GL (Fin 2) F)) 1 0 = 0
    rw [sourceGL2_right_weyl_bottom_left, sourceGL2_right_upper_bottom_right]
    dsimp only [x]
    rw [mul_neg, ← mul_div_assoc, mul_div_cancel_left₀ _ hg, neg_add_cancel]
  · symm
    calc
      _ = g * ((sourceGL2Upper (-x) * ((sourceGL2Weyl : GL (Fin 2) F) * sourceGL2Weyl)) *
          sourceGL2Upper x) := by simp only [b, mul_assoc]
      _ = g := by
        rw [sourceGL2Weyl_square, mul_one, sourceGL2Upper_mul, neg_add_cancel, sourceGL2Upper_zero, mul_one]

end
end ArtinMatthews
