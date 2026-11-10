module

public import ArtinMatthews.SourceKubotaCoordinates
public import ArtinMatthews.SourceKubotaMultipliers
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
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

/-! The extra ordinary scalar in each GL2 identity carries no Kubota
multiplier. This is checked before quotienting the scalar subgroup. -/

namespace ArtinMatthews
open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups
noncomputable section
variable {F : Type*} [Field F] {A : Type*} [CommGroup A]
    (B : Fˣ →* (Fˣ →* A))

private theorem div_unit_mul (u d : Fˣ) : u / (u * d) = d⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_inv]
  abel

theorem sourceKP2Multiplier_Bruhat_scalar (u : Fˣ)
    (hdiag : ∀ x, B x x = 1) (hminusL : ∀ x, B (sourceMinusOneUnit F) x = 1)
    (hminusR : ∀ x, B x (sourceMinusOneUnit F) = 1) :
    sourceKP2Multiplier B (sourceGL2Diagonal (sourceBruhatDiagonal u))
      (GeneralLinearGroup.scalar (Fin 2) u) = 1 := by
  rw [sourceKP2Multiplier, sourceKubotaX_mul_scalar, sourceKubotaX_diagonal,
    sourceKubotaX_scalar, sourceGL2Diagonal_det, GeneralLinearGroup.det_scalar,
    Fintype.card_fin, one_mul, div_one, div_unit_mul, sourceBruhatDiagonal_units]
  simp [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.pow_apply, hdiag, hminusL, hminusR]

theorem sourceKP2Multiplier_Weyl_scalar (u : Fˣ)
    (hdiag : ∀ x, B x x = 1) (hminusL : ∀ x, B (sourceMinusOneUnit F) x = 1)
    (hminusR : ∀ x, B x (sourceMinusOneUnit F) = 1) :
    sourceKP2Multiplier B (sourceGL2Diagonal u⁻¹ * sourceGL2Weyl)
      (GeneralLinearGroup.scalar (Fin 2) u) = 1 := by
  rw [sourceKP2Multiplier, sourceKubotaX_mul_scalar, sourceKubotaX_diagonal_weyl,
    sourceKubotaX_scalar, map_mul, sourceGL2Diagonal_det, sourceGL2Weyl_det,
    GeneralLinearGroup.det_scalar, Fintype.card_fin, one_mul, div_one, div_unit_mul,
    _root_.mul_inv_rev, inv_inv, sourceMinusOneUnit_inv]
  simp [MonoidHom.mul_apply, MonoidHom.inv_apply, hdiag, hminusL, hminusR]

end
end ArtinMatthews
