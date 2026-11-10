module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
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

/-! Literal root, torus and Weyl elements in the actual projective
linear group. The scalar in the Bruhat identity is proved before
passing to PGL2. No assertion about lifts to a full cover is used. -/

namespace ArtinMatthews
open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups
noncomputable section
variable {F : Type*} [Field F]

def sourceGL2Upper (x : F) : GL (Fin 2) F :=
  mkOfDetNeZero !![1, x; 0, 1] (by simp [Matrix.det_fin_two])

def sourceGL2Lower (x : F) : GL (Fin 2) F :=
  mkOfDetNeZero !![1, 0; x, 1] (by simp [Matrix.det_fin_two])

def sourceGL2Diagonal (u : Fˣ) : GL (Fin 2) F :=
  mkOfDetNeZero !![(u : F), 0; 0, 1] (by simp [Matrix.det_fin_two])

def sourceGL2Weyl : GL (Fin 2) F :=
  mkOfDetNeZero !![0, 1; 1, 0] (by simp [Matrix.det_fin_two])

def sourceBruhatDiagonal (u : Fˣ) : Fˣ :=
  Units.mk0 (-((u : F)⁻¹) ^ 2) (neg_ne_zero.mpr (pow_ne_zero 2 (inv_ne_zero (Units.ne_zero u))))

theorem sourceGL2Upper_mul_diagonal (x : F) (u : Fˣ) :
    sourceGL2Upper x * sourceGL2Diagonal u =
      sourceGL2Diagonal u * sourceGL2Upper (x / (u : F)) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceGL2Upper, sourceGL2Diagonal, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

theorem sourceGL2Weyl_mul_diagonal (u : Fˣ) :
    sourceGL2Weyl * sourceGL2Diagonal u =
      sourceGL2Diagonal u⁻¹ * sourceGL2Weyl * GeneralLinearGroup.scalar (Fin 2) u := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceGL2Weyl, sourceGL2Diagonal, Matrix.mul_apply, Fin.sum_univ_two,
      GeneralLinearGroup.coe_scalar, Matrix.diagonal_apply]

theorem sourceGL2Weyl_mul_upper_scalar (u : Fˣ) :
    sourceGL2Weyl * sourceGL2Upper (u : F) =
      sourceGL2Upper ((u : F)⁻¹) * sourceGL2Diagonal (sourceBruhatDiagonal u) *
        sourceGL2Lower ((u : F)⁻¹) * GeneralLinearGroup.scalar (Fin 2) u := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceGL2Weyl, sourceGL2Upper, sourceGL2Lower, sourceGL2Diagonal, sourceBruhatDiagonal,
      Matrix.mul_apply, Fin.sum_univ_two, GeneralLinearGroup.coe_scalar, Matrix.diagonal_apply]
  ring

abbrev sourcePGL2Upper (x : F) : PGL(2, F) := ProjGenLinGroup.mk (sourceGL2Upper x)
abbrev sourcePGL2Lower (x : F) : PGL(2, F) := ProjGenLinGroup.mk (sourceGL2Lower x)
abbrev sourcePGL2Diagonal (u : Fˣ) : PGL(2, F) := ProjGenLinGroup.mk (sourceGL2Diagonal u)
abbrev sourcePGL2Weyl : PGL(2, F) := ProjGenLinGroup.mk sourceGL2Weyl

theorem sourcePGL2Upper_mul_diagonal (x : F) (u : Fˣ) :
    sourcePGL2Upper x * sourcePGL2Diagonal u =
      sourcePGL2Diagonal u * sourcePGL2Upper (x / (u : F)) := by
  simpa only [map_mul] using congrArg (ProjGenLinGroup.mk (n := Fin 2) (R := F))
    (sourceGL2Upper_mul_diagonal x u)

theorem sourcePGL2Weyl_diagonal (u : Fˣ) :
    sourcePGL2Weyl * sourcePGL2Diagonal u * (sourcePGL2Weyl : PGL(2, F))⁻¹ =
      sourcePGL2Diagonal u⁻¹ := by
  have h : sourcePGL2Weyl * sourcePGL2Diagonal u = sourcePGL2Diagonal u⁻¹ * sourcePGL2Weyl := by
    simpa only [map_mul, ProjGenLinGroup.mk_scalar, mul_one] using
      congrArg (ProjGenLinGroup.mk (n := Fin 2) (R := F)) (sourceGL2Weyl_mul_diagonal u)
  rw [h, mul_assoc, mul_inv_cancel, mul_one]

theorem sourcePGL2Weyl_mul_upper (u : Fˣ) :
    sourcePGL2Weyl * sourcePGL2Upper (u : F) =
      sourcePGL2Upper ((u : F)⁻¹) * sourcePGL2Diagonal (sourceBruhatDiagonal u) *
        sourcePGL2Lower ((u : F)⁻¹) := by
  simpa only [map_mul, ProjGenLinGroup.mk_scalar, mul_one] using
    congrArg (ProjGenLinGroup.mk (n := Fin 2) (R := F)) (sourceGL2Weyl_mul_upper_scalar u)

end
end ArtinMatthews
