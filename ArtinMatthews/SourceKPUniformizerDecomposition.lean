module

public import Mathlib.RingTheory.Valuation.Basic
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


set_option backward.privateInPublic true
@[expose] public section

/-! The integer valuation and unit part relative to a genuine
uniformizer. The sign is fixed so that a uniformizer has order one. -/

namespace ArtinMatthews
open scoped ValuativeRel
noncomputable section
variable {F : Type*} [Field F] (ν : Valuation F (WithZero (Multiplicative ℤ)))

def sourceKPValuationOrder (y : Fˣ) : ℤ :=
  -WithZero.expEquiv.symm (Units.map ν.toMonoidHom y)

theorem sourceKPValuationOrder_spec (y : Fˣ) :
    ν (y : F) = WithZero.exp (-sourceKPValuationOrder ν y) := by
  unfold sourceKPValuationOrder
  rw [neg_neg]
  change ν (y : F) =
    ((WithZero.expEquiv (WithZero.expEquiv.symm (Units.map ν.toMonoidHom y)) :
      (WithZero (Multiplicative ℤ))ˣ) : WithZero (Multiplicative ℤ))
  rw [Equiv.apply_symm_apply]
  rfl

theorem sourceKPValuationOrder_eq (y : Fˣ) (n : ℤ) :
    sourceKPValuationOrder ν y = n ↔ ν (y : F) = WithZero.exp (-n) := by
  rw [sourceKPValuationOrder_spec ν y, WithZero.exp_inj, neg_inj]

theorem sourceKPValuationOrder_one : sourceKPValuationOrder ν 1 = 0 := by
  apply (sourceKPValuationOrder_eq ν 1 0).mpr
  simp

theorem sourceKPValuationOrder_mul (y z : Fˣ) :
    sourceKPValuationOrder ν (y * z) = sourceKPValuationOrder ν y + sourceKPValuationOrder ν z := by
  apply (sourceKPValuationOrder_eq ν (y * z) _).mpr
  rw [Units.val_mul, map_mul, sourceKPValuationOrder_spec ν y, sourceKPValuationOrder_spec ν z,
    ← WithZero.exp_add, neg_add]

theorem sourceKPValuationOrder_zpow (y : Fˣ) (n : ℤ) :
    sourceKPValuationOrder ν (y ^ n) = n * sourceKPValuationOrder ν y := by
  apply (sourceKPValuationOrder_eq ν (y ^ n) _).mpr
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, sourceKPValuationOrder_spec ν y, ← WithZero.exp_zsmul]
  congr 1
  simp

theorem sourceKPValuationOrder_of_unit (y : Fˣ) (hy : ν (y : F) = 1) :
    sourceKPValuationOrder ν y = 0 := by
  apply (sourceKPValuationOrder_eq ν y 0).mpr
  simpa only [neg_zero, WithZero.exp_zero] using hy

def sourceKPUnitPart (π y : Fˣ) : Fˣ := y / π ^ sourceKPValuationOrder ν y

theorem sourceKPUnitPart_factor (π y : Fˣ) :
    π ^ sourceKPValuationOrder ν y * sourceKPUnitPart ν π y = y := by
  unfold sourceKPUnitPart
  rw [mul_comm, div_mul_cancel]

theorem sourceKPUnitPart_mul (π y z : Fˣ) :
    sourceKPUnitPart ν π (y * z) = sourceKPUnitPart ν π y * sourceKPUnitPart ν π z := by
  rw [sourceKPUnitPart, sourceKPValuationOrder_mul, zpow_add]
  exact (div_mul_div_comm _ _ _ _).symm

theorem sourceKPUnitPart_of_unit (π y : Fˣ) (hy : ν (y : F) = 1) :
    sourceKPUnitPart ν π y = y := by
  rw [sourceKPUnitPart, sourceKPValuationOrder_of_unit ν y hy, zpow_zero, div_one]

theorem sourceKPUnitPart_of_uniformizer_zpow (π : Fˣ) (hπ : ν (π : F) = WithZero.exp (-1 : ℤ))
    (n : ℤ) : sourceKPUnitPart ν π (π ^ n) = 1 := by
  have h := (sourceKPValuationOrder_eq ν π 1).mpr hπ
  rw [sourceKPUnitPart, sourceKPValuationOrder_zpow, h, mul_one, div_self']

theorem sourceKPUnitPart_valuation (π : Fˣ) (hπ : ν (π : F) = WithZero.exp (-1 : ℤ)) (y : Fˣ) :
    ν (sourceKPUnitPart ν π y : F) = 1 := by
  have h := (sourceKPValuationOrder_eq ν π 1).mpr hπ
  have hp : ν ((π ^ sourceKPValuationOrder ν y : Fˣ) : F) = ν (y : F) := by
    rw [sourceKPValuationOrder_spec ν (π ^ sourceKPValuationOrder ν y),
      sourceKPValuationOrder_zpow, h, mul_one, ← sourceKPValuationOrder_spec ν y]
  have hy : ν (y : F) ≠ 0 := by
    rw [sourceKPValuationOrder_spec ν y]
    exact WithZero.exp_ne_zero
  rw [sourceKPUnitPart, Units.val_div_eq_div_val, map_div₀, hp, div_self hy]

end
end ArtinMatthews
