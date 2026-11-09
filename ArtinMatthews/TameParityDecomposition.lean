module

public import ArtinMatthews.IntegerConductor


set_option backward.privateInPublic true
@[expose] public section

/-! The actual unit/prime decomposition reduced to valuation parity. -/

namespace ArtinMatthews.QuadraticWeil

open LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField
open ArtinMatthews.QuadraticGauss
open scoped ValuativeRel Classical

noncomputable section

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

theorem tameParityDecomposition (x : Kˣ) :
    x = (integerUnitsToFieldUnits K (tameUnitFactor K x) *
        tameUniformizer K ^ (valuationMap K (Additive.ofMul x) % 2)) *
      (tameUniformizer K ^ (valuationMap K (Additive.ofMul x) / 2)) ^ 2 := by
  let m := valuationMap K (Additive.ofMul x)
  have hm : m = m % 2 + (m / 2) * 2 := by omega
  calc
    x = integerUnitsToFieldUnits K (tameUnitFactor K x) * tameUniformizer K ^ m :=
      (tameUnitFactor_decomposition K x).symm
    _ = _ := by
      rw [mul_assoc]
      congr 1
      calc
        tameUniformizer K ^ m = tameUniformizer K ^ (m % 2 + (m / 2) * 2) := congrArg _ hm
        _ = _ := by rw [zpow_add, zpow_mul]; rfl

end

end ArtinMatthews.QuadraticWeil
