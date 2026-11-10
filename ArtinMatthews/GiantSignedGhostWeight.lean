module

public import Mathlib.Basic.Real.Basic
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

/-! A single exponential memory weight controls the forward and reversed
ghost coefficients, including doubled original births. -/
namespace ArtinMatthews
noncomputable section

theorem giantSignedGhostWeight_exists (aMax cMax dMax : ℝ) (ha : aMax < 1) :
    ∃ v : ℝ, 1 < v ∧ ∀ A C D : ℝ,
      A ≤ aMax → |C| ≤ cMax → |D| ≤ dMax →
        A + |D| / v < 1 ∧ A + 2 * |C| / v < 1 := by
  let R := max dMax (2 * cMax)
  let v := max 2 ((R + 1) / (1 - aMax))
  have hv : 1 < v := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hv0 : 0 < v := lt_trans (by norm_num) hv
  have heps : 0 < 1 - aMax := sub_pos.mpr ha
  have hRv : R + 1 ≤ v * (1 - aMax) :=
    (div_le_iff₀ heps).mp (le_max_right _ _)
  have hdiv : R / v < 1 - aMax := (div_lt_iff₀ hv0).mpr (by nlinarith)
  refine ⟨v, hv, ?_⟩
  intro A C D hA hC hD
  have hDv : |D| / v ≤ R / v :=
    (div_le_div_iff_of_pos_right hv0).mpr (hD.trans (le_max_left _ _))
  have hCv : 2 * |C| / v ≤ R / v :=
    (div_le_div_iff_of_pos_right hv0).mpr
      ((mul_le_mul_of_nonneg_left hC (by norm_num)).trans (le_max_right _ _))
  constructor <;> linarith

theorem giantSignedGhost_source_A_lt_one {q ρ : ℝ} (hρ : 0 < ρ) (hq : q < ρ ^ 2) :
    q / ρ ^ 2 < 1 := by
  exact (div_lt_one (sq_pos_of_pos hρ)).mpr hq

end
end ArtinMatthews
