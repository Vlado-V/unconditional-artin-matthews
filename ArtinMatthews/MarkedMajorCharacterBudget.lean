module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import ArtinMatthews.MarkedMajorArcRoughLowBudget
public import ArtinMatthews.MarkedRoughCharacterRange
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

/-! The genuine finite six-character cost is absorbed by a stronger instance
of the arbitrary-saving source estimate. -/
namespace ArtinMatthews
open Filter

 theorem markedMajor_character_cost {L a P Y X : ℝ} {q : ℕ}
    (hL : 0 < L) (hq : (q:ℝ) ≤ L^a) (hY : 0 ≤ Y) (hX : 0 ≤ X) :
    (q:ℝ)^6*((Y*X)*L^(-(P+6*a))) ≤ (Y*X)*L^(-P) := by
  have hq6 : (q:ℝ)^6 ≤ L^(6*a) := by
    calc
      _ ≤ (L^a)^6 := pow_le_pow_left₀ (Nat.cast_nonneg q) hq 6
      _ = L^(6*a) := by simpa only [Nat.cast_ofNat,mul_comm] using (Real.rpow_mul_natCast hL.le a 6).symm
  calc
    _ ≤ L^(6*a)*((Y*X)*L^(-(P+6*a))) :=
      mul_le_mul_of_nonneg_right hq6 (mul_nonneg (mul_nonneg hY hX) (Real.rpow_nonneg hL.le _))
    _ = (Y*X)*L^(-P) := by
      rw [mul_left_comm,← Real.rpow_add hL]
      congr 2
      ring

 theorem markedMajor_arc_unit_scale (a τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ L : ℝ in atTop, L^a ≤ Real.exp (L^(6/25:ℝ)) ∧
      Real.exp (L^(6/25:ℝ)) ≤ Real.exp (τ*L) := by
  filter_upwards [marked_polynomial_le_exp_rpow 1 a (6/25) (by norm_num),
    marked_rough_cutoff_scale (6/25) τ (by norm_num) hτ] with L hq hW
  exact ⟨by simpa only [one_mul] using hq,hW⟩

end ArtinMatthews
