module

public import ArtinMatthews.IdealResidualFamily
public import ArtinMatthews.IdealSourceBlocks
public import ArtinMatthews.IdealSourceProbeCaps
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! The actual residual family has uniform fresh-label and collision counts. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealSourceResidual_freshCount {G : Type*} [Fintype G] [DecidableEq G]
    (S T : Finset G) {m J ell : ℕ} (hm : m ≤ J) (ν : IdealResidualPattern G J)
    (hν : ν ∈ idealResidualPatterns (idealSourceProbes S hm) (idealSourceProbes T hm)) :
    (∑ g, ((idealResidualCopied ν g).card + ell)) ≤ Fintype.card G * (m + ell) := by
  calc
    _ ≤ ∑ _g : G, (m + ell) := sum_le_sum fun g _ =>
      Nat.add_le_add_right (idealSourceResidualCopied_card_le S T hm ν hν g) ell
    _ = _ := by simp

theorem idealSourceResidual_comparisonCount {G : Type*} [Fintype G] [DecidableEq G]
    (S T : Finset G) {m J ell : ℕ} (hm : m ≤ J) (ν : IdealResidualPattern G J)
    (hν : ν ∈ idealResidualPatterns (idealSourceProbes S hm) (idealSourceProbes T hm)) :
    (∑ g, (idealResidualCopied ν g).card) * (2 * (J + ell)) ≤
      (Fintype.card G * m) * (2 * (J + ell)) := by
  have hs : (∑ g, (idealResidualCopied ν g).card) ≤ Fintype.card G * m := by
    calc
      _ ≤ ∑ _g : G, m := sum_le_sum fun g _ =>
        idealSourceResidualCopied_card_le S T hm ν hν g
      _ = _ := by simp
  exact Nat.mul_le_mul_right _ hs

theorem idealSource_group_count_polynomial {L C₀ : ℝ} {b K : ℕ}
    (hL : 1 ≤ L) (hC₀ : 0 ≤ C₀) (hCL : C₀ ≤ L)
    (hb : (b : ℝ) ≤ C₀ * Real.log L) (hK : (K : ℝ) ≤ L) :
    ((b * K : ℕ) : ℝ) ≤ L ^ (3 : ℕ) := by
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hlog : Real.log L ≤ L :=
    (Real.log_le_sub_one_of_pos hLpos).trans (by linarith)
  have hb2 : (b : ℝ) ≤ L ^ (2 : ℕ) := by
    calc
      _ ≤ C₀ * Real.log L := hb
      _ ≤ C₀ * L := mul_le_mul_of_nonneg_left hlog hC₀
      _ ≤ L * L := mul_le_mul_of_nonneg_right hCL hLpos.le
      _ = _ := by ring
  rw [Nat.cast_mul]
  calc
    _ ≤ L ^ (2 : ℕ) * L := mul_le_mul hb2 hK (Nat.cast_nonneg _) (sq_nonneg L)
    _ = _ := by ring

end
end ArtinMatthews
