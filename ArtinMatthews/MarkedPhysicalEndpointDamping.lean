module

public import ArtinMatthews.MarkedPhysicalEndpointState
public import ArtinMatthews.MarkedPhysicalEndpointVectors
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
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Boundary damping identities for the actual union of band primes and
the exact empty-memory raw state. -/
noncomputable section
open scoped BigOperators
namespace ArtinMatthews

theorem markedPhysical_bandCount_union {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (hdis : Pairwise (fun j l => Disjoint (P j) (P l))) (u : ℕ) :
    bandCount (Finset.univ.biUnion P) u = ∑ j, bandCount (P j) u := by
  classical
  have heq : activeDivisors (Finset.univ.biUnion P) u =
      Finset.univ.biUnion (fun j => activeDivisors (P j) u) := by
    ext p
    simp only [activeDivisors, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact exists_and_right.symm
  rw [bandCount, heq]
  apply Finset.card_biUnion
  intro i _ j _ hij
  exact (hdis hij).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

/-- The endpoint damping really counts the original union of prime bands,
with the original real half-excess exponent. -/
theorem markedPhysicalEndpointDamping_eq_union {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    (M : ℕ) (q : ℝ) (z : ℤ × ℤ) :
    markedPhysicalEndpointDamping P M q z =
      q ^ (((bandCount (Finset.univ.biUnion P) z.1.natAbs : ℝ) - Fintype.card J * M) / 2) := by
  rw [markedPhysical_bandCount_union P hdis]
  rfl

/-- At every position the physical endpoint vector absorbs the original
damping exactly, including the zero-support case. -/
theorem markedPhysicalEndpointVector_damped {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (M : ℕ) (q : ℝ) (α β : ℕ → ℂ) (z : ℤ × ℤ) :
    (markedPhysicalEndpointDamping P M q z : ℂ) * markedPhysicalEndpointVector P M α β z =
      markedPhysicalEndpointVector P M α β z := by
  classical
  by_cases hz : MarkedPhysicalEndpointSupport P M z.1.natAbs
  · rw [markedPhysicalEndpointDamping_of_support P M q z hz]
    simp
  · simp only [markedPhysicalEndpointVector, ite_eq_right hz, mul_zero]

theorem markedPhysicalEmptyMemory_hits {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) :
    markedRawPendingHits (markedPhysicalEmptyMemory P) z hz = 0 := by
  unfold markedRawPendingHits
  apply Finset.sum_eq_zero
  intro j _
  apply Finset.sum_eq_zero
  intro k _
  exact Fin.elim0 k

/-- The exact physical boundary vector in the raw representation. Original
primitive/divisibility/distinctness tests remain in the physical state; the
empty-memory pending factor is identically one. -/
theorem markedPhysicalStateToRaw_endpoint {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (hP : ∀ j p, p ∈ P j → p.Prime)
    (M : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (ρ : ℝ) (α β : ℕ → ℂ) (s : MarkedPhysicalState P M Z) :
    markedRawEndpointFactor hZ ρ
      (fun t => markedPhysicalEndpointVector P M α β t.1.1)
      (markedPhysicalStateToRaw P hP M Z s) =
      markedPhysicalEndpointVector P M α β s.1.1.1 := by
  classical
  rw [markedRawEndpointFactor, ite_eq_left (markedPhysicalStateToRaw_distinct P hP M Z s)]
  change (((ρ ^ markedRawPendingHits (markedPhysicalEmptyMemory _) _ _ : ℝ) : ℂ) * _) = _
  rw [markedPhysicalEmptyMemory_hits, pow_zero, Complex.ofReal_one, one_mul]
  rfl

end ArtinMatthews
