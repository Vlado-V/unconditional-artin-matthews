module

public import Mathlib.Analysis.Complex.Norm
public import ArtinMatthews.MarkedMinorArcRawGhostChoiceCauchy
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
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

/-! A bounded multiplier on each literal choice preserves the absolute
Cauchy majorant. This statement gives a crude estimate only; it makes no
claim that a signed cancellation estimate survives an arbitrary modifier. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators

theorem markedChoiceModifier_finite_cauchy {ι : Type*} [Fintype ι]
    (c f modifier : ι → ℂ) (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hm : ∀ i, ‖modifier i‖ ≤ 1) :
    ‖∑ i, c i*(modifier i*f i)‖^2 ≤
      (∑ i, ‖c i‖*w i)*(∑ i, ‖c i‖/w i*‖f i‖^2) := by
  apply (markedGhostChoice_finite_cauchy c (fun i => modifier i*f i) w hw).trans
  apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (hw i).le))
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (norm_nonneg _) (hw i).le)
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right (hm i) (norm_nonneg _)).trans_eq (one_mul _)

end ArtinMatthews
