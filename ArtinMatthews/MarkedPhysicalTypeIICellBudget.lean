module

public import ArtinMatthews.MarkedMinorArcProductMassActual
public import ArtinMatthews.MarkedPhysicalCellRootBudget
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

/-! The actual .21 source scale controls the cell factor for the
unchanged N=2ceil(sqrt(log x)/2), including scales below one. -/
namespace ArtinMatthews
noncomputable section

theorem markedPhysicalTypeII_cell_root_bound {x H A : ℝ}
    (hlog : 1 ≤ Real.log x) (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hscale : H ≤ Real.exp (A*(Real.log x)^(21/100:ℝ))) :
    (256*H+1)^((markedMemoryMomentLength x:ℝ)⁻¹) ≤ 257*Real.exp A := by
  let H₁ := max 1 H
  have hH₁ : 1 ≤ H₁ := le_max_left _ _
  have hpos : 0 < H₁ := zero_lt_one.trans_le hH₁
  have hhi : H₁ ≤ Real.exp (A*(Real.log x)^(21/100:ℝ)) :=
    max_le (Real.one_le_exp (mul_nonneg hA (Real.rpow_nonneg (zero_le_one.trans hlog) _))) hscale
  have hl : Real.log H₁ ≤ A*(Real.log x)^(21/100:ℝ) := (Real.log_le_iff_le_exp hpos).mpr hhi
  have hn : (Real.log x)^(1/2:ℝ) ≤ (markedMemoryMomentLength x:ℝ) :=
    markedPhysicalMomentOrder_lower (Real.log x)
  have hb := markedPhysicalCell_root_budget H₁ A (Real.log x) hH₁ hA hlog hl
    (markedMemoryMomentLength x) hn
  exact (Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ 256*H+1)
    (show 256*H+1 ≤ 256*H₁+1 by have hh := le_max_right (1:ℝ) H; dsimp [H₁]; linarith)
    (inv_nonneg.mpr (Nat.cast_nonneg _))).trans hb

end
end ArtinMatthews
