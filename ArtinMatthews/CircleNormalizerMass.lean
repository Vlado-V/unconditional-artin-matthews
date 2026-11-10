module

public import ArtinMatthews.CircleNormalizerDefinitions
public import ArtinMatthews.CircleDetector
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

/-! The actual all-moduli family has linear weight mass. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators

theorem circleModuli_card_le (F r L : ℕ) :
    (circleModuli F r L).card ≤ 3 * L + 1 := by
  apply (Finset.card_filter_le _ _).trans
  rw [Nat.card_Icc]
  omega

theorem circleModuli_card_le_four (F r L : ℕ) (hL : 1 ≤ L) :
    (circleModuli F r L).card ≤ 4 * L := by
  have h := circleModuli_card_le F r L
  omega

theorem circleModuli_weightMass_le (F r L : ℕ) (hL : 1 ≤ L)
    (ω : ℕ → ℝ) (W : ℝ) (hW : 0 ≤ W)
    (hω : ∀ q ∈ circleModuli F r L, ω q ≤ W) :
    circleWeightMass (circleModuli F r L) ω ≤ 4 * W * L := by
  unfold circleWeightMass
  calc
    _ ≤ ∑ _q ∈ circleModuli F r L, W := Finset.sum_le_sum hω
    _ = ((circleModuli F r L).card : ℝ) * W := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (4 * L : ℕ) * W :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast circleModuli_card_le_four F r L hL) hW
    _ = _ := by push_cast; ring

end ArtinMatthews
