module

public import ArtinMatthews.MarkedMemoryStageBirthMass
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeFixedCode
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

/-! The actual memo updates for initial slots, ghost batches and fresh
edge labels. This definitions-only layer is independent of row bounds. -/

noncomputable section
namespace ArtinMatthews

def markedMemoryInitialPivotValues
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes} {M B N : ℕ}
    (old : MarkedMemoryPotentialAddress J M B N → Option Nat.Primes) (active : MarkedRawActive P M) :
    MarkedMemoryPotentialAddress J M B N → Option Nat.Primes :=
  markedMemoryStageBirthValues 0 old markedMemoryInitialDraw markedMemoryInitialDraw_injective
    (fun a => active a.1 a.2)

def markedMemoryGhostPivotValues
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes} {M B N : ℕ}
    (t : Fin (N+1)) (old : MarkedMemoryPotentialAddress J M B N → Option Nat.Primes)
    (l : J → Fin (B+1)) (births : (j : J) → Fin (l j:ℕ) → ↥(P j)) :
    MarkedMemoryPotentialAddress J M B N → Option Nat.Primes :=
  markedMemoryStageBirthValues (2*t.1+1) old (markedMemoryGhostStageDraw t l)
    (markedMemoryGhostStageDraw_injective t l) (fun a => births a.1 a.2)

def markedMemoryEdgePivotValues
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes} {M B N pads : ℕ}
    (t : Fin N) (old : MarkedMemoryPotentialAddress J M B N → Option Nat.Primes)
    {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (s : MarkedRawState P (pads+1) B Z) (c : MarkedRawEdgeChoice hZ s) :
    MarkedMemoryPotentialAddress J M B N → Option Nat.Primes :=
  markedMemoryStageBirthValues (2*t.1+2) old
    (markedMemoryEdgeStageDraw t (markedDirtyEdgePromotedGroups c.promotions))
    (markedMemoryEdgeStageDraw_injective t (markedDirtyEdgePromotedGroups c.promotions))
    (markedDirtyFixedEdgeChoiceCode hZ s (markedDirtyEdgePromotedGroups c.promotions) ⟨c,rfl⟩).2.2.2

end ArtinMatthews
