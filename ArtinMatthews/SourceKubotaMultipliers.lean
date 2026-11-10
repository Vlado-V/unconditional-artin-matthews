module

public import ArtinMatthews.SourceKubotaCoordinates
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

/-! Exact Kubota multipliers for the rank-one root and Bruhat products.
The diagonal and minus-one symbol laws are explicit in this algebraic
lemma. The finite-place specialization derives them from actual CFT. -/

namespace ArtinMatthews
open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups
noncomputable section
variable {F : Type*} [Field F] {A : Type*} [CommGroup A]
    (B : Fˣ →* (Fˣ →* A))

theorem sourceMinusOneUnit_inv : (sourceMinusOneUnit F)⁻¹ = sourceMinusOneUnit F := by
  apply Units.ext
  simp [sourceMinusOneUnit]

theorem sourceBruhatDiagonal_units (u : Fˣ) :
    sourceBruhatDiagonal u = sourceMinusOneUnit F * (u⁻¹)^2 := by
  apply Units.ext
  simp [sourceBruhatDiagonal, sourceMinusOneUnit]

theorem sourceKubotaX_one : sourceKubotaX (1 : GL (Fin 2) F) = 1 := by
  apply Units.ext
  simp [sourceKubotaX, sourceKubotaBottom]

theorem sourceKubotaX_scalar (u : Fˣ) : sourceKubotaX (GeneralLinearGroup.scalar (Fin 2) u) = u := by
  have h := sourceKubotaX_mul_scalar (1 : GL (Fin 2) F) u
  simpa only [one_mul, sourceKubotaX_one] using h

theorem sourceKP2Multiplier_upper_diagonal (x : F) (u : Fˣ) :
    sourceKP2Multiplier B (sourceGL2Upper x) (sourceGL2Diagonal u) = 1 := by
  simp [sourceKP2Multiplier, sourceKubotaX_upper_diagonal, sourceKubotaX_upper,
    sourceKubotaX_diagonal, sourceGL2Upper_det, sourceGL2Diagonal_det]

theorem sourceKP2Multiplier_diagonal_upper (x : F) (u : Fˣ) :
    sourceKP2Multiplier B (sourceGL2Diagonal u) (sourceGL2Upper x) = 1 := by
  simp [sourceKP2Multiplier, sourceKubotaX_diagonal_upper, sourceKubotaX_upper,
    sourceKubotaX_diagonal, sourceGL2Upper_det, sourceGL2Diagonal_det]

theorem sourceKP2Multiplier_weyl_upper (x : F) :
    sourceKP2Multiplier B sourceGL2Weyl (sourceGL2Upper x) = 1 := by
  simp [sourceKP2Multiplier, sourceKubotaX_weyl_upper, sourceKubotaX_weyl,
    sourceKubotaX_upper, sourceGL2Upper_det]

theorem sourceKP2Multiplier_upper_middle (x : F) (u : Fˣ) :
    sourceKP2Multiplier B (sourceGL2Upper x) (sourceBruhatMiddle u) = 1 := by
  simp [sourceKP2Multiplier, sourceKubotaX_upper_middle, sourceKubotaX_upper,
    sourceKubotaX_middle, sourceGL2Upper_det]

theorem sourceKP2Multiplier_Bruhat_last (u : Fˣ)
    (hdiag : ∀ x, B x x = 1) (hminus : ∀ x, B x (sourceMinusOneUnit F) = 1) :
    sourceKP2Multiplier B (sourceGL2Upper ((u : F)⁻¹) * sourceBruhatMiddle u)
      (sourceGL2Lower ((u : F)⁻¹)) = 1 := by
  have hx : sourceKubotaX (sourceGL2Lower ((u : F)⁻¹)) = u⁻¹ := by
    simpa only [Units.val_inv_eq_inv_val] using sourceKubotaX_lower_unit u⁻¹
  have hx' : sourceKubotaX ((sourceGL2Upper ((u : F)⁻¹) * sourceBruhatMiddle u) *
      sourceGL2Lower ((u : F)⁻¹)) = 1 := by
    rw [← sourceGL2Weyl_mul_upper_middle, sourceKubotaX_weyl_upper]
  have hd : (1 : Fˣ) / (u⁻¹ * sourceMinusOneUnit F) = u * sourceMinusOneUnit F := by
    rw [one_div, _root_.mul_inv_rev, inv_inv, sourceMinusOneUnit_inv, mul_comm]
  rw [sourceKP2Multiplier, hx', sourceKubotaX_upper_middle, hx,
    map_mul, sourceGL2Upper_det, sourceBruhatMiddle_det, one_mul, sourceGL2Lower_det, hd]
  simp [MonoidHom.inv_apply, hdiag, hminus]

theorem sourceKP2Multiplier_weyl_diagonal (u : Fˣ)
    (hdiag : ∀ x, B x x = 1) (hminusL : ∀ x, B (sourceMinusOneUnit F) x = 1)
    (hminusR : ∀ x, B x (sourceMinusOneUnit F) = 1) :
    sourceKP2Multiplier B sourceGL2Weyl (sourceGL2Diagonal u) = 1 := by
  simp [sourceKP2Multiplier, sourceKubotaX_weyl_diagonal, sourceKubotaX_weyl,
    sourceKubotaX_diagonal, sourceGL2Weyl_det, sourceGL2Diagonal_det,
    div_eq_mul_inv, sourceMinusOneUnit_inv, hdiag, hminusL, hminusR]

theorem sourceKP2Multiplier_diagonal_weyl (u : Fˣ)
    (hminus : ∀ x, B x (sourceMinusOneUnit F) = 1) :
    sourceKP2Multiplier B (sourceGL2Diagonal u) sourceGL2Weyl = 1 := by
  simp [sourceKP2Multiplier, sourceKubotaX_diagonal_weyl, sourceKubotaX_weyl,
    sourceKubotaX_diagonal, sourceGL2Weyl_det, sourceGL2Diagonal_det, hminus]

end
end ArtinMatthews
