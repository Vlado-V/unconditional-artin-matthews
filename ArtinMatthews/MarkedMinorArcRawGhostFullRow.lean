module

public import ArtinMatthews.MarkedMinorArcRawGhostBirthRow
public import ArtinMatthews.MarkedMinorArcRawGhostDeletionRow
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! Genuine full actual ghost weighted absolute row bound. The derivation
sums the literal total-truncated birth choices and actual eligible indexed
old deletions; no row, probability, or operator bound is a premise. -/
namespace ArtinMatthews
open scoped BigOperators

/-- Actual old deletion factors are nonnegative in the source parameter range. -/
theorem markedRawGhostDeletionFactor_nonneg {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} {qStage ρ v₀ : ℝ}
    (hq₀ : 0 ≤ qStage) (hq₁ : qStage ≤ 1) (hρ : 0 < ρ) (hv₀ : 0 < v₀)
    (m : MarkedRawMemory P B) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (del : MarkedRawGhostDeletion m) (j : J) :
    0 ≤ markedRawGhostDeletionFactor qStage ρ v₀ m z hz del j := by
  exact mul_nonneg
    (pow_nonneg (div_nonneg (sub_nonneg.mpr hq₁) (mul_pos hρ hv₀).le) _)
    (pow_nonneg (div_nonneg hq₀ (sq_nonneg _)) _)

/-- Exact source exponential-survival upper bound for the literal ghost
absolute row with Schur weight v₀^(total pending size). No degree-dependent
factor is discarded or substituted, even with repeated indexed values. -/
theorem markedRawGhost_actual_weighted_row {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (hν : ∀ j p, 0 ≤ ν j p)
    (V : J → ℝ) (hV : ∀ j, 0 ≤ V j) {qStage ρ v₀ : ℝ}
    (hq₀ : 0 ≤ qStage) (hq₁ : qStage ≤ 1) (hρ : 0 < ρ) (hv₀ : 0 < v₀)
    {B : ℕ} (m : MarkedRawMemory P B) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) :
    markedRawGhostWeightedAbsRow ν V qStage ρ v₀ m z hz ≤
      (∏ j, Real.exp ((v₀*(1-qStage)*V j/ρ)*(∑ p : P j, ν j p)))*
        ∏ j, (qStage/ρ^2+(1-qStage)/(ρ*v₀))^(markedRawGroupHitIndices m j z hz).card := by
  classical
  let E : ℝ := ∏ j, Real.exp ((v₀*(1-qStage)*V j/ρ)*(∑ p : P j, ν j p))
  unfold markedRawGhostWeightedAbsRow
  calc
    _ = ∑ del : MarkedRawGhostDeletion m, if MarkedRawGhostDeletionAllowed m z hz del then
        (∏ j, markedRawGhostDeletionFactor qStage ρ v₀ m z hz del j)*
          ∑ l : MarkedRawGhostBirthSizes m del,
            ∏ j, markedRawGhostBirthFactor ν V qStage ρ v₀ j (l.1 j : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro del _
      split_ifs
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        exact markedRawGhost_absolute_birth_sum ν hν V hV hq₀ hq₁ hρ hv₀ m z hz del l
      · rfl
    _ ≤ ∑ del : MarkedRawGhostDeletion m, if MarkedRawGhostDeletionAllowed m z hz del then
        (∏ j, markedRawGhostDeletionFactor qStage ρ v₀ m z hz del j)*E else 0 := by
      apply Finset.sum_le_sum
      intro del _
      split_ifs
      · exact mul_le_mul_of_nonneg_left
          (markedRawGhost_birth_cap_exponential ν hν V hV hq₁ hρ hv₀ m del)
          (Finset.prod_nonneg (fun j _ => markedRawGhostDeletionFactor_nonneg hq₀ hq₁ hρ hv₀ m z hz del j))
      · exact le_rfl
    _ = (∑ del : MarkedRawGhostDeletion m, if MarkedRawGhostDeletionAllowed m z hz del then
        ∏ j, markedRawGhostDeletionFactor qStage ρ v₀ m z hz del j else 0)*E := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro del _
      split_ifs <;> simp only [zero_mul]
    _ = (∏ j, (qStage/ρ^2+(1-qStage)/(ρ*v₀))^(markedRawGroupHitIndices m j z hz).card)*E := by
      rw [markedRawGhost_deletion_sum]
    _ = _ := mul_comm _ _

end ArtinMatthews
