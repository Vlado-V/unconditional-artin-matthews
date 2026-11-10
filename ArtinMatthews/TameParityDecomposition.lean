module

public import ArtinMatthews.LocalTameGaussSection
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.Topology.Sheaves.Init


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
