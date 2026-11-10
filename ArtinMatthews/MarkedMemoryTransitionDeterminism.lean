module

public import ArtinMatthews.MarkedMemoryHistoryEdgeAccess
public import ArtinMatthews.MarkedMemoryTransitionAssembly
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

/-! A chronological history is determined by its actual local ghost and
edge choices. Applied to the deterministic finite-transition assembler,
this recovers the entire dependent history, including the final ghost,
from its finite vertex accessors. -/
namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)

/-- Every local choice is retained, including both slot permutations
inside each edge choice. No equality of numeric marks is substituted. -/
theorem markedMemoryChronologicalHistory_ext {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history₁ history₂ : MarkedMemoryChronologicalHistory hZ n s)
    (hghost : ∀ v : Fin (n+1), HEq (markedMemoryHistoryVertexGhost hZ history₁ v)
      (markedMemoryHistoryVertexGhost hZ history₂ v))
    (hedge : ∀ v : Fin n, HEq (markedMemoryHistoryVertexEdge hZ history₁ v)
      (markedMemoryHistoryVertexEdge hZ history₂ v)) : history₁ = history₂ := by
  induction n generalizing s with
  | zero => exact eq_of_heq (hghost 0)
  | succ n ih =>
    rcases history₁ with ⟨ghost₁, edge₁, tail₁⟩
    rcases history₂ with ⟨ghost₂, edge₂, tail₂⟩
    have hg : ghost₁ = ghost₂ := eq_of_heq (hghost 0)
    subst ghost₂
    have he : edge₁ = edge₂ := eq_of_heq (hedge 0)
    subst edge₂
    have ht : tail₁ = tail₂ := ih tail₁ tail₂
      (fun v => hghost v.succ) (fun v => hedge v.succ)
    cases ht
    rfl

theorem markedMemoryChronologicalHistory_eq_iff_vertexChoices {n : ℕ}
    {s : MarkedRawState P (pads+1) B Z}
    (history₁ history₂ : MarkedMemoryChronologicalHistory hZ n s) :
    history₁ = history₂ ↔
      (∀ v : Fin (n+1), HEq (markedMemoryHistoryVertexGhost hZ history₁ v)
        (markedMemoryHistoryVertexGhost hZ history₂ v)) ∧
      (∀ v : Fin n, HEq (markedMemoryHistoryVertexEdge hZ history₁ v)
        (markedMemoryHistoryVertexEdge hZ history₂ v)) := by
  constructor
  · intro h
    cases h
    exact ⟨fun _ => HEq.rfl, fun _ => HEq.rfl⟩
  · rintro ⟨hg, he⟩
    exact markedMemoryChronologicalHistory_ext hZ history₁ history₂ hg he

theorem markedMemoryChronologicalHistory_hext {n : ℕ}
    {s t : MarkedRawState P (pads+1) B Z} (hstate : s = t)
    (history₁ : MarkedMemoryChronologicalHistory hZ n s)
    (history₂ : MarkedMemoryChronologicalHistory hZ n t)
    (hghost : ∀ v : Fin (n+1), HEq (markedMemoryHistoryVertexGhost hZ history₁ v)
      (markedMemoryHistoryVertexGhost hZ history₂ v))
    (hedge : ∀ v : Fin n, HEq (markedMemoryHistoryVertexEdge hZ history₁ v)
      (markedMemoryHistoryVertexEdge hZ history₂ v)) : HEq history₁ history₂ := by
  cases hstate
  exact heq_of_eq (markedMemoryChronologicalHistory_ext hZ history₁ history₂ hghost hedge)

theorem markedMemoryHistoryTransport_heq {n : ℕ}
    {s t : MarkedRawState P (pads+1) B Z} (hstate : s = t)
    (history : MarkedMemoryChronologicalHistory hZ n s) :
    HEq (markedMemoryHistoryTransport hZ hstate history) history := by
  cases hstate
  rfl

variable {N : ℕ} (d : MarkedMemoryFiniteTransitions (P := P) (pads := pads) (B := B) hZ N)

theorem markedMemoryFiniteTransitions_segment_eq_of_vertexChoices
    (remaining start : ℕ) (hbound : start+remaining ≤ N)
    (history : MarkedMemoryChronologicalHistory hZ remaining (d.state start (by omega)))
    (hghost : ∀ v : Fin (remaining+1), HEq (markedMemoryHistoryVertexGhost hZ history v)
      (d.ghost (start+v.val) (by omega)))
    (hedge : ∀ v : Fin remaining, HEq (markedMemoryHistoryVertexEdge hZ history v)
      (d.edge (start+v.val) (by omega))) :
    markedMemoryFiniteTransitions_segment hZ d remaining start hbound = history := by
  apply markedMemoryChronologicalHistory_ext hZ
  · intro v
    exact (markedMemoryFiniteTransitions_segment_vertexGhost hZ d remaining start hbound v).trans
      (hghost v).symm
  · intro v
    exact (markedMemoryFiniteTransitions_segment_vertexEdge hZ d remaining start hbound v).trans
      (hedge v).symm

theorem markedMemoryFiniteTransitions_segment_heq_of_vertexChoices
    (remaining start : ℕ) (hbound : start+remaining ≤ N)
    {s : MarkedRawState P (pads+1) B Z} (hstate : d.state start (by omega) = s)
    (history : MarkedMemoryChronologicalHistory hZ remaining s)
    (hghost : ∀ v : Fin (remaining+1), HEq (markedMemoryHistoryVertexGhost hZ history v)
      (d.ghost (start+v.val) (by omega)))
    (hedge : ∀ v : Fin remaining, HEq (markedMemoryHistoryVertexEdge hZ history v)
      (d.edge (start+v.val) (by omega))) :
    HEq (markedMemoryFiniteTransitions_segment hZ d remaining start hbound) history := by
  apply markedMemoryChronologicalHistory_hext hZ hstate
  · intro v
    exact (markedMemoryFiniteTransitions_segment_vertexGhost hZ d remaining start hbound v).trans
      (hghost v).symm
  · intro v
    exact (markedMemoryFiniteTransitions_segment_vertexEdge hZ d remaining start hbound v).trans
      (hedge v).symm

theorem markedMemoryFiniteTransitions_segment_transport_eq_of_vertexChoices
    (remaining start : ℕ) (hbound : start+remaining ≤ N)
    {s : MarkedRawState P (pads+1) B Z} (hstate : d.state start (by omega) = s)
    (history : MarkedMemoryChronologicalHistory hZ remaining s)
    (hghost : ∀ v : Fin (remaining+1), HEq (markedMemoryHistoryVertexGhost hZ history v)
      (d.ghost (start+v.val) (by omega)))
    (hedge : ∀ v : Fin remaining, HEq (markedMemoryHistoryVertexEdge hZ history v)
      (d.edge (start+v.val) (by omega))) :
    markedMemoryHistoryTransport hZ hstate
      (markedMemoryFiniteTransitions_segment hZ d remaining start hbound) = history :=
  eq_of_heq ((markedMemoryHistoryTransport_heq hZ hstate _).trans
    (markedMemoryFiniteTransitions_segment_heq_of_vertexChoices hZ d remaining start hbound
      hstate history hghost hedge))

theorem markedMemoryFiniteTransitions_history_eq_of_vertexChoices
    (history : MarkedMemoryChronologicalHistory hZ N (d.state 0 (Nat.zero_le N)))
    (hghost : ∀ v : Fin (N+1), HEq (markedMemoryHistoryVertexGhost hZ history v)
      (d.ghost v.val (by omega)))
    (hedge : ∀ v : Fin N, HEq (markedMemoryHistoryVertexEdge hZ history v)
      (d.edge v.val (by omega))) :
    markedMemoryFiniteTransitions_history hZ d = history := by
  apply markedMemoryChronologicalHistory_ext hZ
  · intro v
    exact (markedMemoryFiniteTransitions_history_vertexGhost hZ d v).trans (hghost v).symm
  · intro v
    exact (markedMemoryFiniteTransitions_history_vertexEdge hZ d v).trans (hedge v).symm

theorem markedMemoryFiniteTransitions_history_heq_of_vertexChoices
    {s : MarkedRawState P (pads+1) B Z} (hstate : d.state 0 (Nat.zero_le N) = s)
    (history : MarkedMemoryChronologicalHistory hZ N s)
    (hghost : ∀ v : Fin (N+1), HEq (markedMemoryHistoryVertexGhost hZ history v)
      (d.ghost v.val (by omega)))
    (hedge : ∀ v : Fin N, HEq (markedMemoryHistoryVertexEdge hZ history v)
      (d.edge v.val (by omega))) :
    HEq (markedMemoryFiniteTransitions_history hZ d) history := by
  apply markedMemoryChronologicalHistory_hext hZ hstate
  · intro v
    exact (markedMemoryFiniteTransitions_history_vertexGhost hZ d v).trans (hghost v).symm
  · intro v
    exact (markedMemoryFiniteTransitions_history_vertexEdge hZ d v).trans (hedge v).symm

theorem markedMemoryFiniteTransitions_history_transport_eq_of_vertexChoices
    {s : MarkedRawState P (pads+1) B Z} (hstate : d.state 0 (Nat.zero_le N) = s)
    (history : MarkedMemoryChronologicalHistory hZ N s)
    (hghost : ∀ v : Fin (N+1), HEq (markedMemoryHistoryVertexGhost hZ history v)
      (d.ghost v.val (by omega)))
    (hedge : ∀ v : Fin N, HEq (markedMemoryHistoryVertexEdge hZ history v)
      (d.edge v.val (by omega))) :
    markedMemoryHistoryTransport hZ hstate (markedMemoryFiniteTransitions_history hZ d) = history :=
  eq_of_heq ((markedMemoryHistoryTransport_heq hZ hstate _).trans
    (markedMemoryFiniteTransitions_history_heq_of_vertexChoices hZ d hstate history hghost hedge))

end
end ArtinMatthews
