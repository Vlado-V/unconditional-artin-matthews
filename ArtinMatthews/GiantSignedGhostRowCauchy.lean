module

public import ArtinMatthews.GiantSignedGhostMoves
public import ArtinMatthews.GiantSignedGhostPositiveApply
public import ArtinMatthews.CountableWeightedCauchy
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! Weighted Cauchy for the actual unbounded ghost row. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem giantSignedGhostMoves_norm_weight_summable {P : Finset ℕ}
    (ν : P → ℝ) (hν : ∀ p, 0 ≤ ν p) (A C D : ℂ)
    (F : GiantSignedGroupMemory P → ℝ) (hF0 : ∀ m, 0 ≤ F m)
    (B u : ℝ) (hB : 0 ≤ B) (hu : 0 ≤ u)
    (hF : ∀ m, F m ≤ B * u ^ m.1) (m : GiantSignedGroupMemory P) :
    Summable (fun r : GiantSignedGhostMoves m =>
      ‖giantSignedGhostMoveCoefficient ν A C D m r‖ * F (giantSignedGhostMoveTarget m r)) := by
  apply Complex.summable_ofReal.mp
  have hs := (giantSignedGhostMoves_summable_norm ν hν
    (‖A‖ : ℂ) (‖C‖ : ℂ) (‖D‖ : ℂ) (fun t => (F t : ℂ)) B u hB hu
    (fun t => by simpa only [Complex.norm_real, Real.norm_of_nonneg (hF0 t)] using hF t) m).of_norm
  simpa only [Complex.ofReal_mul, giantSignedGhostMoveCoefficient_norm ν hν A C D m] using hs

theorem giantSignedGhostMoves_norm_weight_tsum {P : Finset ℕ}
    (ν : P → ℝ) (hν : ∀ p, 0 ≤ ν p) (A C D : ℂ)
    (F : GiantSignedGroupMemory P → ℝ) (hF0 : ∀ m, 0 ≤ F m)
    (B u : ℝ) (hB : 0 ≤ B) (hu : 0 ≤ u)
    (hF : ∀ m, F m ≤ B * u ^ m.1) (m : GiantSignedGroupMemory P) :
    (∑' r : GiantSignedGhostMoves m,
      ‖giantSignedGhostMoveCoefficient ν A C D m r‖ * F (giantSignedGhostMoveTarget m r)) =
      giantSignedGhostPositiveApply ν ‖A‖ ‖C‖ ‖D‖ F m := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_tsum, giantSignedGhostPositiveApply_coe]
  simp_rw [Complex.ofReal_mul, giantSignedGhostMoveCoefficient_norm ν hν A C D m]
  exact giantSignedGhostMoves_tsum ν hν (‖A‖ : ℂ) (‖C‖ : ℂ) (‖D‖ : ℂ)
    (fun t => (F t : ℂ)) B u hB hu
    (fun t => by simpa only [Complex.norm_real, Real.norm_of_nonneg (hF0 t)] using hF t) m

theorem giantSignedGhostGroupApply_weighted_cauchy {P : Finset ℕ}
    (ν : P → ℝ) (hν : ∀ p, 0 ≤ ν p) (A C D : ℂ)
    (f : GiantSignedGroupMemory P → ℂ) (B u v : ℝ)
    (hB : 0 ≤ B) (hu : 0 ≤ u) (hv : 0 < v)
    (hf : ∀ m, ‖f m‖ ≤ B * u ^ m.1) (m : GiantSignedGroupMemory P) :
    ‖giantSignedGhostGroupApply ν A C D f m‖ ^ 2 ≤
      giantSignedGhostPositiveApply ν ‖A‖ ‖C‖ ‖D‖ (fun t => v ^ t.1) m *
        giantSignedGhostPositiveApply ν ‖A‖ ‖C‖ ‖D‖ (giantSignedGhostCauchyTest f v) m := by
  let c := giantSignedGhostMoveCoefficient ν A C D m
  let target := giantSignedGhostMoveTarget m
  have hc := (giantSignedGhostMoves_summable_norm ν hν A C D f B u hB hu hf m).of_norm
  have hw := giantSignedGhostMoves_norm_weight_summable ν hν A C D
    (fun t => v ^ t.1) (fun _ => pow_nonneg hv.le _) 1 v zero_le_one hv.le
    (fun _ => by simp only [one_mul]; exact le_rfl) m
  have hg := giantSignedGhostMoves_norm_weight_summable ν hν A C D
    (giantSignedGhostCauchyTest f v) (giantSignedGhostCauchyTest_nonneg f v hv.le)
    (B ^ 2) (u ^ 2 / v) (sq_nonneg _) (div_nonneg (sq_nonneg _) hv.le)
    (giantSignedGhostCauchyTest_bound f B u v hv hf) m
  have hcg : Summable (fun r : GiantSignedGhostMoves m =>
      ‖c r‖ * ‖f (target r)‖ ^ 2 / v ^ (target r).1) := by
    simpa only [giantSignedGhostCauchyTest, mul_div_assoc] using hg
  have h := countableWeightedCauchy c (fun r => f (target r))
    (fun r => v ^ (target r).1) (fun r => pow_pos hv _) hc hw hcg
  rw [giantSignedGhostMoves_tsum ν hν A C D f B u hB hu hf m] at h
  rw [giantSignedGhostMoves_norm_weight_tsum ν hν A C D
    (fun t => v ^ t.1) (fun _ => pow_nonneg hv.le _) 1 v zero_le_one hv.le
    (fun _ => by simp only [one_mul]; exact le_rfl) m] at h
  have he := giantSignedGhostMoves_norm_weight_tsum ν hν A C D
    (giantSignedGhostCauchyTest f v) (giantSignedGhostCauchyTest_nonneg f v hv.le)
    (B ^ 2) (u ^ 2 / v) (sq_nonneg _) (div_nonneg (sq_nonneg _) hv.le)
    (giantSignedGhostCauchyTest_bound f B u v hv hf) m
  have he' : (∑' r : GiantSignedGhostMoves m,
      ‖c r‖ * ‖f (target r)‖ ^ 2 / v ^ (target r).1) =
      giantSignedGhostPositiveApply ν ‖A‖ ‖C‖ ‖D‖ (giantSignedGhostCauchyTest f v) m := by
    simpa only [c, target, giantSignedGhostCauchyTest, mul_div_assoc] using he
  rw [he'] at h
  exact h

end
end ArtinMatthews
