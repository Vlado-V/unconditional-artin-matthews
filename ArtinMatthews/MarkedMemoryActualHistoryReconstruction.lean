module

public import ArtinMatthews.MarkedMemoryIndependentHistory
public import ArtinMatthews.MarkedMemoryActualSlotOrder
public import ArtinMatthews.MarkedMemoryActualEdgeReconstruction
public import ArtinMatthews.MarkedMemoryActualGhostReconstruction
public import ArtinMatthews.MarkedMemoryActualStateReconstruction
public import ArtinMatthews.MarkedMemoryTransitionDeterminism
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

/-! Forward extraction followed by independent reconstruction gives the
original chronological history, with every ordered coordinate retained. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
  (history : MarkedMemoryChronologicalHistory hZ n s)
  (ha : MarkedMemoryHistoryAnchorAdmissible hZ history)

local notation "tableau" => markedMemoryActualTableau hZ history ha
local notation "order" => markedMemoryActualOrder hZ history ha

theorem markedMemoryActualTableau_initial :
    markedMemoryIndependentState hZ tableau 0 (Nat.zero_le n) = s :=
  markedMemoryActualTableau_state hZ history ha 0 (Nat.zero_le n)

omit [DecidableEq J] in
theorem markedMemoryActualEdgeTransport_heq
    {a b : MarkedRawState P (pads+1) B Z} (h : a = b) (e : MarkedMemoryEdgeChoice hZ a) :
    HEq e (markedMemoryEdgeTransport hZ h e) := by
  cases h
  rfl

theorem markedMemoryActualHistory_reconstruction :
    markedMemoryHistoryTransport hZ (markedMemoryActualTableau_initial hZ history ha)
      (markedMemoryIndependentHistory hZ tableau order) = history := by
  apply markedMemoryFiniteTransitions_history_transport_eq_of_vertexChoices hZ
    (markedMemoryIndependentTransitions hZ tableau order)
    (markedMemoryActualTableau_initial hZ history ha) history
  · intro v
    exact (markedMemoryActualTableau_ghost_heq hZ history ha v).symm
  · intro v
    exact (markedMemoryActualTableau_edge_heq hZ history ha v).symm.trans
      (markedMemoryActualEdgeTransport_heq hZ
        (markedMemoryIndependentGhost_target hZ tableau v.val (Nat.le_of_lt v.2)).symm
        (markedMemoryIndependentEdge hZ tableau v.val v.2 (order v)))

/-- Every original-history functional, including its exact signed weight
and arbitrary ordered terminal observable, is preserved by reconstruction. -/
theorem markedMemoryActualHistory_functional {R : Type*}
    (F : MarkedMemoryChronologicalHistory hZ n s → R) :
    F (markedMemoryHistoryTransport hZ (markedMemoryActualTableau_initial hZ history ha)
      (markedMemoryIndependentHistory hZ tableau order)) = F history :=
  congrArg F (markedMemoryActualHistory_reconstruction hZ history ha)

theorem markedMemoryActualHistory_covered :
    history ∈ Set.range (fun ordering : Fin n → J → Equiv.Perm (Fin pads) =>
      markedMemoryHistoryTransport hZ (markedMemoryActualTableau_initial hZ history ha)
        (markedMemoryIndependentHistory hZ tableau ordering)) :=
  ⟨order,markedMemoryActualHistory_reconstruction hZ history ha⟩


/-- Nonzero literal coefficients provide the required anchor admissibility;
no initial-memory, numeric-distinctness or image-coverage premise is added. -/
theorem markedMemoryActualHistory_exists_tableau_of_weight_ne_zero
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) (j : ℕ)
    (hw : markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n j history ≠ 0) :
    ∃ (d : MarkedMemoryIndependentLifespans (A := MarkedMemoryActualFiber hZ history)
        (P := P) (pads := pads) (B := B) hZ n)
      (ordering : Fin n → J → Equiv.Perm (Fin pads))
      (hstart : markedMemoryIndependentState hZ d 0 (Nat.zero_le n) = s),
      markedMemoryHistoryTransport hZ hstart (markedMemoryIndependentHistory hZ d ordering) = history := by
  let hadm := markedMemoryHistoryAnchorAdmissible_of_weight_ne_zero ν V hZ ψ η d₀ Y Q ρ qStage χ n j history hw
  exact ⟨markedMemoryActualTableau hZ history hadm,markedMemoryActualOrder hZ history hadm,
    markedMemoryActualTableau_initial hZ history hadm,markedMemoryActualHistory_reconstruction hZ history hadm⟩

end
end ArtinMatthews
