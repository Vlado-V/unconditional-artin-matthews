module

public import ArtinMatthews.MarkedMemoryTiltPrimewise
public import ArtinMatthews.MarkedMinorArcProductMass
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Literal before/after ghost extensions for a nonempty active interval.
Every internal inactive visit keeps its original damping factor. -/
noncomputable section
open scoped BigOperators
namespace ArtinMatthews
attribute [local instance] Classical.propDecidable

def markedMemoryPrefixGhost {N : ℕ} {Λ : Type*} [DecidableEq Λ]
    (η : Fin (N+1) → ℝ) (line : Fin (N+1) → Λ) (a : Fin (N+1)) : ℝ :=
  1 - ∑ h ∈ markedMemoryBefore N a, η h * markedLineHit line h (line a) *
    ∏ j ∈ Finset.univ.filter (fun j => h<j ∧ j<a), (1-η j*markedLineHit line j (line a))

def markedMemorySuffixGhost {N : ℕ} {Λ : Type*} [DecidableEq Λ]
    (η : Fin (N+1) → ℝ) (line : Fin (N+1) → Λ) (a c : Fin (N+1)) : ℝ :=
  1 - ∑ h ∈ markedMemoryAfter N c, η h * markedLineHit line h (line a) *
    ∏ j ∈ Finset.univ.filter (fun j => c<j ∧ j<h), (1-η j*markedLineHit line j (line a))

def markedMemoryInternalDamping {N : ℕ} {Λ : Type*} [DecidableEq Λ]
    (A : Finset (Fin (N+1))) (η : Fin (N+1) → ℝ) (line : Fin (N+1) → Λ)
    (a c : Fin (N+1)) : ℝ :=
  ∏ j ∈ markedMemoryInternal A a c, (1-η j*markedLineHit line j (line a))

theorem markedMemoryPrefixGhost_eq {N : ℕ} {Λ : Type*} [DecidableEq Λ]
    (η : Fin (N+1) → ℝ) (line : Fin (N+1) → Λ) (a : Fin (N+1)) :
    (∏ j ∈ markedMemoryBefore N a, (1-η j*markedLineHit line j (line a))) =
      markedMemoryPrefixGhost η line a :=
  marked_memory_prefix Finset.univ (fun j => η j*markedLineHit line j (line a)) a

theorem markedMemorySuffixGhost_eq {N : ℕ} {Λ : Type*} [DecidableEq Λ]
    (η : Fin (N+1) → ℝ) (line : Fin (N+1) → Λ) (a c : Fin (N+1)) :
    (∏ j ∈ markedMemoryAfter N c, (1-η j*markedLineHit line j (line a))) =
      markedMemorySuffixGhost η line a c :=
  marked_memory_suffix Finset.univ (fun j => η j*markedLineHit line j (line a)) c

/-- Exact source nonempty-active primewise identity: common-line indicator,
one optional earlier ghost, literal internal inactive damping, and one
optional later ghost. No compatibility condition is assumed in advance. -/
theorem markedMemoryPrimeFactor_active_ghosts {N : ℕ} {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (A : Finset (Fin (N+1))) (hA : A.Nonempty) (η : Fin (N+1) → ℝ)
    (line : Fin (N+1) → Λ) :
    markedMemoryPrimeFactor A η line =
      (1 / (Fintype.card Λ : ℝ)) *
        (if MarkedMemoryActiveCoherent A line (A.min' hA) then
          markedMemoryPrefixGhost η line (A.min' hA) *
          markedMemoryInternalDamping A η line (A.min' hA) (A.max' hA) *
          markedMemorySuffixGhost η line (A.min' hA) (A.max' hA) else 0) := by
  rw [markedMemoryPrimeFactor_active A η line _ (A.min'_mem hA),
    markedMemory_inactive_product A hA (fun j => 1-η j*markedLineHit line j (line (A.min' hA))),
    markedMemoryPrefixGhost_eq, markedMemorySuffixGhost_eq]
  rfl

/-- Source damping is exactly q_j on an inactive hit and one on a miss. -/
theorem markedMemory_damping_hit_iff {N : ℕ} {Λ : Type*} [DecidableEq Λ]
    (q : ℝ) (line : Fin (N+1) → Λ) (a j : Fin (N+1)) :
    1-markedMemoryEta q N j*markedLineHit line j (line a) =
      if line j = line a then markedMemoryVisitQ q N j else 1 := by
  by_cases h : line j = line a
  · simp [markedLineHit, h, markedMemoryEta]
  · simp [markedLineHit, h, Ne.symm h]

end ArtinMatthews
