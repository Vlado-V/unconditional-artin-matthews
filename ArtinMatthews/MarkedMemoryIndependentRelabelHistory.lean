module

public import ArtinMatthews.MarkedMemoryIndependentHistory
public import ArtinMatthews.MarkedMemoryIndependentRelabel
public import ArtinMatthews.MarkedMemoryIndependentRelabelEdge
public import ArtinMatthews.MarkedMemoryIndependentRelabelGhost
public import ArtinMatthews.MarkedMemoryTransitionDeterminism
public import ArtinMatthews.MarkedMemoryTransitionDeterminismAccessors
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

/-! Relabeling independent identities preserves the entire reconstructed
chronological history, for the same copied-slot orders. The equality is
proved from literal local choices and the deterministic assembler. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {A A' : J → Type*}
  [∀ j, DecidableEq (A j)] [∀ j, Fintype (A j)]
  [∀ j, DecidableEq (A' j)] [∀ j, Fintype (A' j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (e : (j : J) → A j ≃ A' j)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)

theorem markedMemoryRelabelEdgeTransport_heq
    {s t : MarkedRawState P (pads+1) B Z} (h : s = t) (edge : MarkedMemoryEdgeChoice hZ s) :
    HEq (markedMemoryEdgeTransport hZ h edge) edge := by
  cases h
  rfl

theorem markedMemoryIndependentRelabel_history_heq (order : Fin n → J → Equiv.Perm (Fin pads)) :
    HEq (markedMemoryIndependentHistory hZ (markedMemoryIndependentRelabel hZ e d) order)
      (markedMemoryIndependentHistory hZ d order) := by
  apply markedMemoryChronologicalHistory_hext hZ
    (markedMemoryIndependentRelabel_state hZ e d 0 (Nat.zero_le n))
  · intro v
    exact (markedMemoryFiniteTransitions_history_vertexGhost hZ
      (markedMemoryIndependentTransitions hZ (markedMemoryIndependentRelabel hZ e d) order) v).trans
      ((markedMemoryIndependentRelabel_ghost_heq hZ e d v.val (by omega)).trans
        (markedMemoryFiniteTransitions_history_vertexGhost hZ
          (markedMemoryIndependentTransitions hZ d order) v).symm)
  · intro v
    have hn := markedMemoryRelabelEdgeTransport_heq hZ
      (markedMemoryIndependentGhost_target hZ (markedMemoryIndependentRelabel hZ e d) v.val (Nat.le_of_lt v.2)).symm
      (markedMemoryIndependentEdge hZ (markedMemoryIndependentRelabel hZ e d) v.val v.2 (order v))
    have ho := markedMemoryRelabelEdgeTransport_heq hZ
      (markedMemoryIndependentGhost_target hZ d v.val (Nat.le_of_lt v.2)).symm
      (markedMemoryIndependentEdge hZ d v.val v.2 (order v))
    exact (markedMemoryFiniteTransitions_history_vertexEdge hZ
      (markedMemoryIndependentTransitions hZ (markedMemoryIndependentRelabel hZ e d) order) v).trans
      (hn.trans ((markedMemoryIndependentRelabel_edge_heq hZ e d v.val v.2 (order v)).trans
        (ho.symm.trans (markedMemoryFiniteTransitions_history_vertexEdge hZ
          (markedMemoryIndependentTransitions hZ d order) v).symm)))

theorem markedMemoryIndependentRelabel_history (order : Fin n → J → Equiv.Perm (Fin pads)) :
    markedMemoryHistoryTransport hZ (markedMemoryIndependentRelabel_state hZ e d 0 (Nat.zero_le n))
      (markedMemoryIndependentHistory hZ (markedMemoryIndependentRelabel hZ e d) order) =
        markedMemoryIndependentHistory hZ d order :=
  eq_of_heq ((markedMemoryHistoryTransport_heq hZ
    (markedMemoryIndependentRelabel_state hZ e d 0 (Nat.zero_le n)) _).trans
    (markedMemoryIndependentRelabel_history_heq hZ e d order))

omit e [∀ j, DecidableEq (A' j)] [∀ j, Fintype (A' j)] in
theorem markedMemoryIndependentRelabelFin_history_heq (order : Fin n → J → Equiv.Perm (Fin pads)) :
    HEq (markedMemoryIndependentHistory hZ (markedMemoryIndependentRelabelFin hZ d) order)
      (markedMemoryIndependentHistory hZ d order) :=
  markedMemoryIndependentRelabel_history_heq hZ (fun j => Fintype.equivFin (A j)) d order

end
end ArtinMatthews
