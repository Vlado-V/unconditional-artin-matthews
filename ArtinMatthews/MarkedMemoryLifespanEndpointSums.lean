module

public import ArtinMatthews.MarkedMemoryTiltPrimewiseActual
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

/-! Exact finite endpoint sums for the scalar factors already attached to
indexed histories. An optional endpoint is either absent or one genuine
vertex in the strict before/after range. Orphan endpoints are strictly
ordered, and every internal inactive vertex retains its damping factor. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev MarkedMemoryPrefixChoice {N : ℕ} (a : Fin (N+1)) :=
  Option ↥(markedMemoryBefore N a)

abbrev MarkedMemorySuffixChoice {N : ℕ} (c : Fin (N+1)) :=
  Option ↥(markedMemoryAfter N c)

def markedMemoryPrefixChoiceScalar {N : ℕ} (u : Fin (N+1) → ℝ) (a : Fin (N+1)) :
    MarkedMemoryPrefixChoice a → ℝ
  | none => 1
  | some b => -u b.1 * ∏ v ∈ Finset.univ.filter (fun v => b.1 < v ∧ v < a), (1-u v)

def markedMemorySuffixChoiceScalar {N : ℕ} (u : Fin (N+1) → ℝ) (c : Fin (N+1)) :
    MarkedMemorySuffixChoice c → ℝ
  | none => 1
  | some d => -u d.1 * ∏ v ∈ Finset.univ.filter (fun v => c < v ∧ v < d.1), (1-u v)

theorem markedMemoryPrefixChoice_some_lt {N : ℕ} {a : Fin (N+1)}
    (b : ↥(markedMemoryBefore N a)) : b.1 < a := (Finset.mem_filter.mp b.2).2

theorem markedMemorySuffixChoice_some_lt {N : ℕ} {c : Fin (N+1)}
    (d : ↥(markedMemoryAfter N c)) : c < d.1 := (Finset.mem_filter.mp d.2).2

theorem markedMemoryPrefixChoiceScalar_sum {N : ℕ} (u : Fin (N+1) → ℝ) (a : Fin (N+1)) :
    (∑ choice : MarkedMemoryPrefixChoice a, markedMemoryPrefixChoiceScalar u a choice) =
      ∏ v ∈ markedMemoryBefore N a, (1-u v) := by
  rw [Fintype.sum_option]
  change 1 + (∑ b : ↥(markedMemoryBefore N a),
    -u b.1 * ∏ v ∈ Finset.univ.filter (fun v => b.1 < v ∧ v < a), (1-u v)) = _
  rw [Finset.sum_coe_sort (s := markedMemoryBefore N a)
    (f := fun b => -u b * ∏ v ∈ Finset.univ.filter (fun v => b < v ∧ v < a), (1-u v))]
  have ht := marked_memory_prefix (Finset.univ : Finset (Fin (N+1))) u a
  change (∏ v ∈ markedMemoryBefore N a, (1-u v)) = _ at ht
  rw [ht]
  simp only [neg_mul, Finset.sum_neg_distrib]
  unfold markedMemoryBefore
  ring

theorem markedMemorySuffixChoiceScalar_sum {N : ℕ} (u : Fin (N+1) → ℝ) (c : Fin (N+1)) :
    (∑ choice : MarkedMemorySuffixChoice c, markedMemorySuffixChoiceScalar u c choice) =
      ∏ v ∈ markedMemoryAfter N c, (1-u v) := by
  rw [Fintype.sum_option]
  change 1 + (∑ d : ↥(markedMemoryAfter N c),
    -u d.1 * ∏ v ∈ Finset.univ.filter (fun v => c < v ∧ v < d.1), (1-u v)) = _
  rw [Finset.sum_coe_sort (s := markedMemoryAfter N c)
    (f := fun d => -u d * ∏ v ∈ Finset.univ.filter (fun v => c < v ∧ v < d), (1-u v))]
  have ht := marked_memory_suffix (Finset.univ : Finset (Fin (N+1))) u c
  change (∏ v ∈ markedMemoryAfter N c, (1-u v)) = _ at ht
  rw [ht]
  simp only [neg_mul, Finset.sum_neg_distrib]
  unfold markedMemoryAfter
  ring

abbrev MarkedMemoryActiveEndpointChoice {N : ℕ} (A : Finset (Fin (N+1))) (hA : A.Nonempty) :=
  MarkedMemoryPrefixChoice (A.min' hA) × MarkedMemorySuffixChoice (A.max' hA)

def markedMemoryActiveEndpointScalar {N : ℕ} (A : Finset (Fin (N+1))) (hA : A.Nonempty)
    (u : Fin (N+1) → ℝ) (choice : MarkedMemoryActiveEndpointChoice A hA) : ℝ :=
  markedMemoryPrefixChoiceScalar u (A.min' hA) choice.1 *
    (∏ v ∈ markedMemoryInternal A (A.min' hA) (A.max' hA), (1-u v)) *
    markedMemorySuffixChoiceScalar u (A.max' hA) choice.2

/-- The endpoint sum includes every strict before/after vertex and all
internal gaps, with no assumed endpoint-choice coverage. -/
theorem markedMemoryActiveEndpoint_sum {N : ℕ} (A : Finset (Fin (N+1))) (hA : A.Nonempty)
    (u : Fin (N+1) → ℝ) :
    (∑ choice : MarkedMemoryActiveEndpointChoice A hA, markedMemoryActiveEndpointScalar A hA u choice) =
      ∏ v ∈ Finset.univ \ A, (1-u v) := by
  rw [Fintype.sum_prod_type]
  simp only [markedMemoryActiveEndpointScalar]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [← Finset.sum_mul, markedMemoryPrefixChoiceScalar_sum, markedMemorySuffixChoiceScalar_sum]
  simpa only [mul_assoc] using (markedMemory_inactive_product A hA (fun v => 1-u v)).symm

abbrev MarkedMemoryOrphanEndpointChoice (N : ℕ) :=
  Σ b : Fin (N+1), ↥(Finset.univ.filter (fun d : Fin (N+1) => b < d))

def markedMemoryOrphanEndpointScalar {N : ℕ} {Λ : Type*} [DecidableEq Λ]
    (η : Fin (N+1) → ℝ) (line : Fin (N+1) → Λ) (choice : MarkedMemoryOrphanEndpointChoice N) : ℝ :=
  if line choice.1 = line choice.2.1 then
    (-η choice.1) * (-η choice.2.1) *
      ∏ v ∈ Finset.univ.filter (fun v => choice.1 < v ∧ v < choice.2.1),
        (1-η v*markedLineHit line v (line choice.1))
  else 0

theorem markedMemoryOrphanEndpoint_strict {N : ℕ} (choice : MarkedMemoryOrphanEndpointChoice N) :
    choice.1 < choice.2.1 := (Finset.mem_filter.mp choice.2.2).2

/-- Two negative endpoint factors produce the positive orphan-pair
weight; the strict endpoint type excludes every singleton. -/
theorem markedMemoryOrphanEndpoint_sum {N : ℕ} {Λ : Type*} [DecidableEq Λ]
    (η : Fin (N+1) → ℝ) (line : Fin (N+1) → Λ) :
    (∑ choice : MarkedMemoryOrphanEndpointChoice N, markedMemoryOrphanEndpointScalar η line choice) =
      markedMemoryOrphanGhostSum η line := by
  rw [Fintype.sum_sigma]
  unfold markedMemoryOrphanGhostSum
  apply Finset.sum_congr rfl
  intro b _
  change (∑ d : ↥(Finset.univ.filter (fun d : Fin (N+1) => b < d)),
    if line b = line d.1 then (-η b) * (-η d.1) *
      ∏ v ∈ Finset.univ.filter (fun v => b < v ∧ v < d.1),
        (1-η v*markedLineHit line v (line b)) else 0) = _
  simp only [neg_mul_neg]
  exact Finset.sum_coe_sort (s := Finset.univ.filter (fun d : Fin (N+1) => b < d))
    (f := fun d => if line b = line d then η b * η d *
      ∏ v ∈ Finset.univ.filter (fun v => b < v ∧ v < d),
        (1-η v*markedLineHit line v (line b)) else 0)

end
end ArtinMatthews
