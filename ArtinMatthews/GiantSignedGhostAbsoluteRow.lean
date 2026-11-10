module

public import ArtinMatthews.GiantSignedGhostRow
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

/-! The absolute ghost row on the actual exponential memory weight.
Its series ranges over every birth count and every ordered fresh batch. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem giantSignedGhost_birthSeries_hasSum {P : Finset ℕ}
    (ν : P → ℝ) (C v : ℝ) :
    HasSum (fun b : ℕ => (C ^ b / (Nat.factorial b : ℝ)) *
      (∑ born : Fin b → P, ∏ i, ν (born i)) * v ^ b)
      (Real.exp (C * (∑ p : P, ν p) * v)) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (C * (∑ p : P, ν p) * v)
  rw [← Real.exp_eq_exp_ℝ] at h
  convert h using 1
  funext b
  rw [giantSignedGhost_birthMass, mul_pow, mul_pow]
  ring

theorem giantSignedGhost_birthSeries {P : Finset ℕ}
    (ν : P → ℝ) (C v : ℝ) :
    (∑' b : ℕ, (C ^ b / (Nat.factorial b : ℝ)) *
      (∑ born : Fin b → P, ∏ i, ν (born i)) * v ^ b) =
      Real.exp (C * (∑ p : P, ν p) * v) :=
  (giantSignedGhost_birthSeries_hasSum ν C v).tsum_eq

def giantSignedGhostAbsoluteWeightedRow {P : Finset ℕ}
    (ν : P → ℝ) (A C D v : ℝ) (m : GiantSignedGroupMemory P) : ℝ :=
  ∑ deleted ∈ (giantSignedGhostZeroIndices m).powerset,
    D ^ deleted.card * A ^ ((giantSignedGhostZeroIndices m).card - deleted.card) *
      ∑' b : ℕ, (C ^ b / (Nat.factorial b : ℝ)) *
        ∑ born : Fin b → P, (∏ i, ν (born i)) *
          v ^ (giantSignedGhostTarget m deleted born).1 / v ^ m.1

theorem giantSignedGhostAbsoluteWeightedRow_eq {P : Finset ℕ}
    (ν : P → ℝ) (A C D v : ℝ) (hv : v ≠ 0) (m : GiantSignedGroupMemory P) :
    giantSignedGhostAbsoluteWeightedRow ν A C D v m =
      Real.exp (C * (∑ p : P, ν p) * v) *
        (A + D / v) ^ (giantSignedGhostZeroIndices m).card := by
  classical
  have hi (deleted : Finset (Fin m.1)) (b : ℕ) :
      (∑ born : Fin b → P, (∏ i, ν (born i)) *
        v ^ (giantSignedGhostTarget m deleted born).1 / v ^ m.1) =
          (∑ born : Fin b → P, ∏ i, ν (born i)) * v ^ b / v ^ deleted.card := by
    rw [Finset.sum_mul, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro born _
    rw [mul_div_assoc, giantSignedGhost_degree_weight m deleted born hv, mul_div_assoc]
  have hs (deleted : Finset (Fin m.1)) :
      (∑' b : ℕ, (C ^ b / (Nat.factorial b : ℝ)) *
        ∑ born : Fin b → P, (∏ i, ν (born i)) *
          v ^ (giantSignedGhostTarget m deleted born).1 / v ^ m.1) =
      Real.exp (C * (∑ p : P, ν p) * v) / v ^ deleted.card := by
    simp_rw [hi, ← mul_div_assoc]
    rw [tsum_div_const]
    simp only [← mul_assoc]
    rw [giantSignedGhost_birthSeries]
  unfold giantSignedGhostAbsoluteWeightedRow
  simp_rw [hs]
  calc
    _ = Real.exp (C * (∑ p : P, ν p) * v) *
        ∑ deleted ∈ (giantSignedGhostZeroIndices m).powerset,
          (D / v) ^ deleted.card * A ^ ((giantSignedGhostZeroIndices m).card - deleted.card) := by
      conv_rhs => rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro deleted _
      rw [div_pow]
      ring
    _ = _ := by rw [Finset.sum_pow_mul_eq_add_pow, add_comm (D / v) A]

theorem giantSignedGhostAbsoluteWeightedRow_le {P : Finset ℕ}
    (ν : P → ℝ) (A C D v : ℝ) (hv : 0 < v)
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hcontract : A + D / v ≤ 1)
    (m : GiantSignedGroupMemory P) :
    giantSignedGhostAbsoluteWeightedRow ν A C D v m ≤
      Real.exp (C * (∑ p : P, ν p) * v) := by
  rw [giantSignedGhostAbsoluteWeightedRow_eq ν A C D v (ne_of_gt hv)]
  exact mul_le_of_le_one_right (le_of_lt (Real.exp_pos _))
    (pow_le_one₀ (add_nonneg hA (div_nonneg hD (le_of_lt hv))) hcontract)

end
end ArtinMatthews
