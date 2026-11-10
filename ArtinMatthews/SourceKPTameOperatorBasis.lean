module

public import ArtinMatthews.SourceKPTameOperator
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact action of the tame torus operator on the Jacquet coordinate
basis, and the scalar action when the valuation is divisible by three. -/

namespace ArtinMatthews
noncomputable section

theorem sourceKPTameOperator_basis (Q : ℝ) (z u : ℂˣ) (j : ℤ) (i : ZMod 3) :
    sourceKPTameOperator Q z u j (sourceJacquetBasis i) =
      ((z : ℂ) * sourceJacquetScale Q ((j : ℝ) / 6) *
        (sourceKPCubicPower (A := ℂˣ) u (-(j : ZMod 3) - 2 * i) : ℂ)) •
        sourceJacquetBasis (i + (j : ZMod 3)) := by
  funext t
  let J : ZMod 3 := j
  change (z : ℂ) * sourceJacquetScale Q ((j : ℝ) / 6) *
      (sourceKPCubicPower (A := ℂˣ) u (J - 2 * t) : ℂ) * sourceJacquetBasis i (t - J) =
    ((z : ℂ) * sourceJacquetScale Q ((j : ℝ) / 6) *
      (sourceKPCubicPower (A := ℂˣ) u (-J - 2 * i) : ℂ)) * sourceJacquetBasis (i + J) t
  have he : t - J = i ↔ t = i + J := sub_eq_iff_eq_add
  by_cases h : t = i + J
  · have h0 := he.mpr h
    have hp : J - 2 * t = -J - 2 * i := by
      rw [h, mul_add, two_mul J]
      abel
    rw [hp, h0, h]
    simp only [sourceJacquetBasis, Pi.single_eq_same]
  · have h0 : t - J ≠ i := fun ht => h (he.mp ht)
    simp only [sourceJacquetBasis, Pi.single_eq_of_ne h0, Pi.single_eq_of_ne h, mul_zero]

theorem sourceKPTameOperator_scalar (Q : ℝ) (z : ℂˣ) (j : ℤ) (hj : (j : ZMod 3) = 0)
    (f : ZMod 3 → ℂ) :
    sourceKPTameOperator Q z 1 j f = ((z : ℂ) * sourceJacquetScale Q ((j : ℝ) / 6)) • f := by
  funext i
  change (z : ℂ) * sourceJacquetScale Q ((j : ℝ) / 6) *
      (sourceKPCubicPower (A := ℂˣ) 1 ((j : ZMod 3) - 2 * i) : ℂ) * f (i - (j : ZMod 3)) =
    ((z : ℂ) * sourceJacquetScale Q ((j : ℝ) / 6)) * f i
  rw [sourceKPCubicPower_one, Units.val_one, mul_one, hj]
  exact congrArg (fun t : ZMod 3 => (z : ℂ) * sourceJacquetScale Q ((j : ℝ) / 6) * f t) (sub_zero i)

end
end ArtinMatthews
