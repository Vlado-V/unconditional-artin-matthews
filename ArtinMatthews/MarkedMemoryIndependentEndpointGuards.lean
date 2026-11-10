module

public import ArtinMatthews.MarkedMemoryHistoryAnchorGates
public import ArtinMatthews.MarkedMemoryIndependentHistory
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

/-! Empty actual endpoint memories determine the independent initial
and terminal queues. Anchor admissibility is invariant under the literal
source-state transport used by chronological assembly. -/
namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2)

theorem markedMemoryHistoryAnchor_transport
    {s t : MarkedRawState P (pads+1) B Z} (hs : s=t)
    (H : MarkedMemoryChronologicalHistory hZ n s) :
    MarkedMemoryHistoryAnchorAdmissible hZ (markedMemoryHistoryTransport hZ hs H) ↔
      MarkedMemoryHistoryAnchorAdmissible hZ H := by
  cases hs
  rfl

variable {A : J → Type*} [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)

theorem markedMemoryIndependent_initial_empty_of_sizes
    (hs : ∀ j,((markedMemoryIndependentState hZ d 0 (Nat.zero_le n)).2.2.1.1 j:ℕ)=0) (j : J) :
    (d.lifespan j).initial=[] := by
  apply List.eq_nil_of_length_eq_zero
  exact hs j

theorem markedMemoryIndependent_terminal_empty_of_sizes
    (order : Fin n → J → Equiv.Perm (Fin pads))
    (ht : ∀ j,((markedMemoryChronologicalTarget hZ (markedMemoryIndependentHistory hZ d order)).2.2.1.1 j:ℕ)=0)
    (j : J) : markedMemoryIndependentQueue hZ d (2*n+1) j=[] := by
  apply List.eq_nil_of_length_eq_zero
  have he := congrArg (fun u : MarkedRawState P (pads+1) B Z => (u.2.2.1.1 j:ℕ))
    (markedMemoryIndependentHistory_target hZ d order)
  exact he.symm.trans (ht j)

end
end ArtinMatthews
