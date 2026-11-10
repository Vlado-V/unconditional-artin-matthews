module

public import ArtinMatthews.MarkedMemoryPivotValueDefs
public import ArtinMatthews.MarkedMemoryGhostPivotMass
public import ArtinMatthews.MarkedMemoryEdgePivotMass
public import ArtinMatthews.MarkedMemoryInitialPivotMass
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

/-! Concrete memo updates for the actual initial, ghost and edge draw
tuples. These functions are independent of the permutation; the pivot
gate tests their values only after the current batch has been inserted. -/

noncomputable section
namespace ArtinMatthews

theorem markedMemoryInitialPivotGate_iff
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes} {M B N : ℕ}
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N))
    (old : MarkedMemoryPotentialAddress J M B N → Option Nat.Primes) (active : MarkedRawActive P M) :
    markedMemoryInitialPivotGate σ old active ↔ ∀ a∈markedMemoryStageNonpivots σ 0,
      markedMemoryInitialPivotValues old active a≠none ∧
      markedMemoryInitialPivotValues old active a=markedMemoryInitialPivotValues old active (markedMemoryPotentialPivot σ a) := Iff.rfl

theorem markedMemoryGhostPivotGate_iff
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes} {M B N : ℕ}
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N)) (t : Fin (N+1))
    (old : MarkedMemoryPotentialAddress J M B N → Option Nat.Primes)
    (l : J → Fin (B+1)) (births : (j : J) → Fin (l j:ℕ) → ↥(P j)) :
    markedMemoryGhostPivotGate σ t old l births ↔ ∀ a∈markedMemoryStageNonpivots σ (2*t.1+1),
      markedMemoryGhostPivotValues t old l births a≠none ∧
      markedMemoryGhostPivotValues t old l births a=markedMemoryGhostPivotValues t old l births (markedMemoryPotentialPivot σ a) := Iff.rfl

theorem markedMemoryEdgePivotGate_iff
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes} {M B N pads : ℕ}
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N)) (t : Fin N)
    (old : MarkedMemoryPotentialAddress J M B N → Option Nat.Primes)
    {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (s : MarkedRawState P (pads+1) B Z) (c : MarkedRawEdgeChoice hZ s) :
    markedMemoryEdgePivotGate σ t old hZ s c ↔ ∀ a∈markedMemoryStageNonpivots σ (2*t.1+2),
      markedMemoryEdgePivotValues t old hZ s c a≠none ∧
      markedMemoryEdgePivotValues t old hZ s c a=markedMemoryEdgePivotValues t old hZ s c (markedMemoryPotentialPivot σ a) := Iff.rfl

end ArtinMatthews
