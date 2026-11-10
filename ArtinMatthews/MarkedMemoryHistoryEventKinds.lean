module

public import ArtinMatthews.MarkedMemoryHistoryTrace
public import ArtinMatthews.MarkedMemoryHistoryEdgeSlotDeaths
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

/-! Actual birth/death kinds in the chronological trace. Even transition
times are ghosts; odd transition times are edges. Ghost births/deaths are
pending, whereas fresh edge births and unstored edge deaths are active. -/
namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)

theorem markedMemoryEdgeSlotOrigin_fresh (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedMemoryEdgeChoice hZ s) (birth : MarkedMemoryEdgeBirthIndex choice) :
    markedMemoryEdgeSlotPopulationOrigin hZ s choice
      (Sum.inl ⟨birth.1,(choice.2.2 birth.1).symm (Fin.last pads)⟩) = Sum.inr birth := by
  change Sum.map (markedMemorySlotPopulationEquiv choice.1 s) id
    (markedMemoryEdgePopulationOrigin hZ (markedRawSlotEquiv choice.1 s) choice.2.1
      (Sum.inl ⟨birth.1,choice.2.2 birth.1 ((choice.2.2 birth.1).symm (Fin.last pads))⟩)) = _
  rw [Equiv.apply_symm_apply,
    markedMemoryEdgePopulationOrigin_last_none hZ (markedRawSlotEquiv choice.1 s) choice.2.1 birth.1 birth.2]
  rfl

theorem markedMemoryEdgeSlotOrigin_pending_survives (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedMemoryEdgeChoice hZ s) (j : J) (k : Fin (s.2.2.1.1 j : ℕ)) :
    Sum.inl (Sum.inr ⟨j,k⟩) ∈ Set.range (markedMemoryEdgeSlotPopulationOrigin hZ s choice) := by
  rw [markedMemoryEdgeSlotOrigin_old_range]
  trivial

/-- Ghost births are realized as actual pending particles. -/
theorem markedMemoryHistoryTrace_birth_even {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (t : ℕ)
    (birth : MarkedMemoryHistoryTraceBirth hZ history t) (ht : t % 2 = 0) :
    ∃ j k, markedMemoryHistoryTraceStep hZ history t (Sum.inr ⟨j,k⟩) = Sum.inr birth := by
  induction n generalizing s t with
  | zero =>
    cases t with
    | zero => exact ⟨birth.1,_,markedMemoryGhostPopulationOrigin_birth hZ s history birth.1 birth.2⟩
    | succ t => exact PEmpty.elim birth
  | succ n ih =>
    cases t with
    | zero => exact ⟨birth.1,_,markedMemoryGhostPopulationOrigin_birth hZ s history.1 birth.1 birth.2⟩
    | succ t =>
      cases t with
      | zero => omega
      | succ t => exact ih history.2.2 t birth (by omega)

/-- A genuinely fresh edge label is born in an active target slot. -/
theorem markedMemoryHistoryTrace_birth_odd {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (t : ℕ)
    (birth : MarkedMemoryHistoryTraceBirth hZ history t) (ht : t % 2 = 1) :
    ∃ j k, markedMemoryHistoryTraceStep hZ history t (Sum.inl ⟨j,k⟩) = Sum.inr birth := by
  induction n generalizing s t with
  | zero =>
    cases t with
    | zero => omega
    | succ t => exact PEmpty.elim birth
  | succ n ih =>
    cases t with
    | zero => omega
    | succ t =>
      cases t with
      | zero => exact ⟨birth.1,_,markedMemoryEdgeSlotOrigin_fresh hZ _ history.2.1 birth⟩
      | succ t => exact ih history.2.2 t birth (by omega)

/-- Any old identity disappearing in a ghost step was pending. -/
theorem markedMemoryHistoryTrace_death_even {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (t : ℕ)
    (old : MarkedMemoryPopulationIndex (markedMemoryHistoryTraceState hZ history t))
    (hdead : Sum.inl old ∉ Set.range (markedMemoryHistoryTraceStep hZ history t)) (ht : t % 2 = 0) :
    ∃ j k, old = Sum.inr ⟨j,k⟩ := by
  induction n generalizing s t with
  | zero =>
    cases t with
    | zero =>
      rcases old with ⟨j,k⟩ | ⟨j,k⟩
      · exact False.elim (hdead ⟨Sum.inl ⟨j,k⟩,markedMemoryGhostPopulationOrigin_active hZ s history j k⟩)
      · exact ⟨j,k,rfl⟩
    | succ t => exact False.elim (hdead ⟨old,rfl⟩)
  | succ n ih =>
    cases t with
    | zero =>
      rcases old with ⟨j,k⟩ | ⟨j,k⟩
      · exact False.elim (hdead ⟨Sum.inl ⟨j,k⟩,markedMemoryGhostPopulationOrigin_active hZ s history.1 j k⟩)
      · exact ⟨j,k,rfl⟩
    | succ t =>
      cases t with
      | zero => omega
      | succ t => exact ih history.2.2 t old hdead (by omega)

/-- Edges never kill a pending identity: promotion changes its location.
Any actual old identity dying on an edge was active. -/
theorem markedMemoryHistoryTrace_death_odd {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (t : ℕ)
    (old : MarkedMemoryPopulationIndex (markedMemoryHistoryTraceState hZ history t))
    (hdead : Sum.inl old ∉ Set.range (markedMemoryHistoryTraceStep hZ history t)) (ht : t % 2 = 1) :
    ∃ j k, old = Sum.inl ⟨j,k⟩ := by
  induction n generalizing s t with
  | zero =>
    cases t with
    | zero => omega
    | succ t => exact False.elim (hdead ⟨old,rfl⟩)
  | succ n ih =>
    cases t with
    | zero => omega
    | succ t =>
      cases t with
      | zero =>
        rcases old with ⟨j,k⟩ | ⟨j,k⟩
        · exact ⟨j,k,rfl⟩
        · exact False.elim (hdead (markedMemoryEdgeSlotOrigin_pending_survives hZ _ history.2.1 j k))
      | succ t => exact ih history.2.2 t old hdead (by omega)

end
end ArtinMatthews
