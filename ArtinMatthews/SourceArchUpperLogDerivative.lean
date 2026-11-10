module

public import ArtinMatthews.SourceArchUpperDenominator
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

namespace ArtinMatthews.SourceArchJacquet
open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups
noncomputable section

def sourceArchUpperLog (g : GL (Fin 2) ℂ) (z : ℂ) (t : ℝ) : ℝ :=
  Real.log ‖(GeneralLinearGroup.det g : ℂ)‖ - Real.log (sourceArchUpperDenominator g z t)

def sourceArchUpperLogOne (g : GL (Fin 2) ℂ) (z : ℂ) (t : ℝ) : ℝ :=
  -(sourceArchUpperDenominatorOne g z t / sourceArchUpperDenominator g z t)

def sourceArchUpperLogTwo (g : GL (Fin 2) ℂ) (z : ℂ) (t : ℝ) : ℝ :=
  (sourceArchUpperDenominatorOne g z t / sourceArchUpperDenominator g z t)^2 -
    sourceArchUpperDenominatorTwo g z / sourceArchUpperDenominator g z t

theorem sourceArchUpperLog_eq (g : GL (Fin 2) ℂ) (z : ℂ) (t : ℝ) :
    sourceArchUpperLog g z t = Real.log (sourceArchHeight
      (g * sourceKPUpperMatrix ℂ ((t : ℂ)*z))) := by
  rw [sourceArchHeight_right_upper, Real.log_div
    (norm_ne_zero_iff.mpr (GeneralLinearGroup.det g).ne_zero)
    (sourceArchUpperDenominator_pos g z t).ne']
  rfl

theorem sourceArchUpperLog_hasDerivAt (g : GL (Fin 2) ℂ) (z : ℂ) (t : ℝ) :
    HasDerivAt (sourceArchUpperLog g z) (sourceArchUpperLogOne g z t) t := by
  exact ((sourceArchUpperDenominator_hasDerivAt g z t).log
    (sourceArchUpperDenominator_pos g z t).ne').const_sub _

theorem sourceArchUpperLogOne_hasDerivAt (g : GL (Fin 2) ℂ) (z : ℂ) (t : ℝ) :
    HasDerivAt (sourceArchUpperLogOne g z) (sourceArchUpperLogTwo g z t) t := by
  have h := ((sourceArchUpperDenominatorOne_hasDerivAt g z t).div
    (sourceArchUpperDenominator_hasDerivAt g z t) (sourceArchUpperDenominator_pos g z t).ne').neg
  convert h using 1
  · rfl
  · unfold sourceArchUpperLogTwo
    field_simp [(sourceArchUpperDenominator_pos g z t).ne']
    ring

theorem sourceArchUpperLogOne_bound (g : GL (Fin 2) ℂ) (z : ℂ) (t : ℝ) :
    |sourceArchUpperLogOne g z t| ≤ ‖z‖ := by
  rw [sourceArchUpperLogOne, abs_neg, abs_div,
    abs_of_pos (sourceArchUpperDenominator_pos g z t), div_le_iff₀ (sourceArchUpperDenominator_pos g z t)]
  exact sourceArchUpperDenominatorOne_bound g z t

theorem sourceArchUpperLogTwo_bound (g : GL (Fin 2) ℂ) (z : ℂ) (t : ℝ) :
    |sourceArchUpperLogTwo g z t| ≤ 3*‖z‖^2 := by
  have hq := sourceArchUpperDenominator_pos g z t
  have h1 : |sourceArchUpperDenominatorOne g z t / sourceArchUpperDenominator g z t| ≤ ‖z‖ := by
    simpa only [sourceArchUpperLogOne, abs_neg] using sourceArchUpperLogOne_bound g z t
  have h2 : sourceArchUpperDenominatorTwo g z / sourceArchUpperDenominator g z t ≤ 2*‖z‖^2 :=
    (div_le_iff₀ hq).mpr (sourceArchUpperDenominatorTwo_bound g z t)
  have h2pos : 0 ≤ sourceArchUpperDenominatorTwo g z / sourceArchUpperDenominator g z t :=
    div_nonneg (sourceArchUpperDenominatorTwo_nonneg g z) hq.le
  calc
    |sourceArchUpperLogTwo g z t| ≤
        |(sourceArchUpperDenominatorOne g z t / sourceArchUpperDenominator g z t)^2| +
          |sourceArchUpperDenominatorTwo g z / sourceArchUpperDenominator g z t| := abs_sub _ _
    _ ≤ ‖z‖^2 + 2*‖z‖^2 := by
      rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg h2pos]
      exact add_le_add (by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h1 2) h2
    _ = 3*‖z‖^2 := by ring

end
end ArtinMatthews.SourceArchJacquet
