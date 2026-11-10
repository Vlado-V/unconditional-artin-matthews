module

public import ArtinMatthews.MarkedMinorArcDirtyPending
public import Mathlib.Analysis.Complex.Exponential
public import ArtinMatthews.MarkedMinorArcRawGhostAction
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

/-! Exact indexed deletion polynomial and the actual prime-batch exponential
in the source signed ghost row. These retain the true finite choices and
factorial birth integral; no memory operator norm is assumed. -/
namespace ArtinMatthews
open scoped BigOperators

/-- Deletion versus survival is exactly the subset expansion over eligible
old indices, even when their prime and anchor values repeat. -/
theorem markedRawGhost_deletion_polynomial {n : ℕ} (H : Finset (Fin n)) (a b : ℝ) :
    (∑ del ∈ H.powerset, a^del.card*b^(H \ del).card)=(a+b)^H.card := by
  simpa only [Finset.prod_const] using (Finset.prod_add (fun _ : Fin n => a) (fun _ => b) H).symm

/-- Actual eligible pending indices give the exact source ghost row factor. -/
theorem markedRawGhost_group_deletion_row {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B) (j : J)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (qStage ρ v₀ : ℝ) :
    (∑ del ∈ (markedRawGroupHitIndices m j z hz).powerset,
      ((1-qStage)/(ρ*v₀))^del.card*
        (qStage/ρ^2)^(markedRawGroupHitIndices m j z hz \ del).card)=
      (qStage/ρ^2+(1-qStage)/(ρ*v₀))^(markedRawGroupHitIndices m j z hz).card := by
  rw [markedRawGhost_deletion_polynomial,add_comm]

/-- The actual ordered anchored prime-batch row integral is bounded by the
source exponential, with no extra factor from the projective anchors. -/
theorem markedRawGhost_group_actual_birth_row {P : Finset Nat.Primes} (ν : P → ℝ)
    (hν : ∀ p, 0 ≤ ν p) (c : ℝ) (hc : 0 ≤ c) (B : ℕ) :
    (∑ l ∈ Finset.range (B+1), ∑ births : Fin l → P,
      c^l*(∏ k, ν (births k))/(Nat.factorial l : ℝ)) ≤ Real.exp (c*(∑ p : P, ν p)) := by
  classical
  calc
    _ = ∑ l ∈ Finset.range (B+1), c^l*(∑ p : P, ν p)^l/(Nat.factorial l : ℝ) := by
      apply Finset.sum_congr rfl
      intro l _
      rw [← Finset.sum_div,← Finset.mul_sum,markedRawGhost_group_birth_mass]
    _ ≤ _ := markedRawGhost_group_birth_exponential _ c (Finset.sum_nonneg (fun p _ => hν p)) hc B

/-- The actual independent finite deletion/birth row is at most the exact
PD exponential times its eligible-old-hit survival polynomial. -/
theorem markedRawGhost_group_actual_choice_row {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (hν : ∀ j p, 0 ≤ ν j p)
    {B : ℕ} (m : MarkedRawMemory P B) (j : J) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (V qStage ρ v₀ : ℝ) (hV : 0 ≤ V) (hq₀ : 0 ≤ qStage) (hq₁ : qStage ≤ 1)
    (hρ : 0 < ρ) (hv₀ : 0 < v₀) :
    (∑ del ∈ (markedRawGroupHitIndices m j z hz).powerset,
      ∑ l ∈ Finset.range (B+1), ∑ births : Fin l → ↥(P j),
        ((1-qStage)/(ρ*v₀))^del.card*(qStage/ρ^2)^(markedRawGroupHitIndices m j z hz \ del).card*
          (v₀*(1-qStage)*V/ρ)^l*(∏ k, ν j (births k))/(Nat.factorial l : ℝ)) ≤
      Real.exp ((v₀*(1-qStage)*V/ρ)*(∑ p : P j, ν j p))*
        (qStage/ρ^2+(1-qStage)/(ρ*v₀))^(markedRawGroupHitIndices m j z hz).card := by
  classical
  have hc : 0 ≤ v₀*(1-qStage)*V/ρ := by positivity
  have hrow := markedRawGhost_group_actual_birth_row (ν j) (hν j) _ hc B
  have hfactor : 0 ≤ ∑ del ∈ (markedRawGroupHitIndices m j z hz).powerset,
      ((1-qStage)/(ρ*v₀))^del.card*(qStage/ρ^2)^(markedRawGroupHitIndices m j z hz \ del).card := by
    apply Finset.sum_nonneg
    intro del _
    positivity
  calc
    _ = (∑ del ∈ (markedRawGroupHitIndices m j z hz).powerset,
        ((1-qStage)/(ρ*v₀))^del.card*(qStage/ρ^2)^(markedRawGroupHitIndices m j z hz \ del).card)*
        (∑ l ∈ Finset.range (B+1), ∑ births : Fin l → ↥(P j),
          (v₀*(1-qStage)*V/ρ)^l*(∏ k, ν j (births k))/(Nat.factorial l : ℝ)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro del _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro births _
      ring
    _ ≤ _ := by
      rw [mul_comm,← markedRawGhost_group_deletion_row m j z hz qStage ρ v₀]
      exact mul_le_mul_of_nonneg_right hrow hfactor

end ArtinMatthews
