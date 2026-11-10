module

public import ArtinMatthews.GiantCandidateCoinMass
public import ArtinMatthews.GiantCandidateResidueFullDyad
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
public import Mathlib.NumberTheory.SelbergSieve
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

/-! The discarded mass on a full rough product box is the literal
uniform tuple average of the failed coin mass. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators
noncomputable section

def giantCandidateFullRoughBox {j : ℕ} (x : ℝ) (H : Fin j → ℕ) : Finset (Fin j → ℕ) :=
  Fintype.piFinset (fun i => giantCandidateRoughFullDyad
    (Real.exp ((Real.log x)^(6/25:ℝ))) (H i))

def giantCandidateFailedBoxMean {j : ℕ} (x threshold c q : ℝ) (H : Fin j → ℕ) : ℝ :=
  (∑ t ∈ giantCandidateFullRoughBox x H,
    giantCandidateFailedCoinMass x threshold c q j (∏ i,t i)) /
      ((giantCandidateFullRoughBox x H).card:ℝ)

theorem giantCandidateFailedBoxMean_mul_card {j : ℕ} (x threshold c q : ℝ) (H : Fin j → ℕ) :
    giantCandidateFailedBoxMean x threshold c q H *
      ((giantCandidateFullRoughBox x H).card:ℝ) =
      ∑ t ∈ giantCandidateFullRoughBox x H,giantCandidateFailedCoinMass x threshold c q j (∏ i,t i) := by
  unfold giantCandidateFailedBoxMean
  by_cases h : (giantCandidateFullRoughBox x H).card = 0
  · rw [card_eq_zero.mp h]
    simp
  · exact div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr h)

theorem giantCandidateFailedBoxMean_nonneg_eventually {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (j : ℕ) (hj : 0 < j) :
    ∀ᶠ x : ℝ in atTop,∀ threshold : ℝ,∀ H : Fin j → ℕ,
      0 ≤ giantCandidateFailedBoxMean x threshold (giantCandidateCoinScale q j) q H := by
  filter_upwards [giantCandidateCoinMass_actual_bounds hq0 hq1 j hj] with x hx
  intro threshold H
  exact div_nonneg (sum_nonneg (fun t _ => (hx threshold (∏ i,t i)).2.1)) (Nat.cast_nonneg _)

end
end ArtinMatthews
